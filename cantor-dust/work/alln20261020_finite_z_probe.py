"""Floating discovery of all-scale coefficient covers at finite Z.

This is not a certificate. The interval extrema implement the exact
monotonicity lemma in alln20261020_finite_phase_transfer.md.
"""
import json
import math
import time
from pathlib import Path
import numpy as np
from alln20261020_inner_phase_probe import prefixes, BANDS, modular_gaps


def good_cell(numerator, minimum_z, height=3, depth=4, inset=1e-10):
    c_lo, c_hi = (2*numerator-1)/4000, (2*numerator+1)/4000
    center = 3.**height/2
    vlo = (2+prefixes(depth))/3
    vw = 3.**(-depth-1)
    lower, upper = [], []
    for p in range(max(0, depth+height-2), depth+height+4):
        aw = 3.**(height-p)
        a = 3.**height*prefixes(p)
        rlo = c_lo*aw*vlo/(vw*(1+(a[:, None]+aw)/minimum_z))
        rhi = c_hi*aw*(vlo+vw)/vw
        good = np.zeros_like(rlo, dtype=bool)
        for lo, hi in BANDS:
            good |= (rlo>lo)&(rhi[None, :]<hi)
        if not np.any(good):
            continue
        # Supremum of each lower image corner, infimum of each upper.
        hl_inf = center-a-aw
        hu_inf = center-a
        hl_z = minimum_z*np.log1p((center-a-aw)/(minimum_z+a+aw))
        hu_z = minimum_z*np.log1p((center-a)/(minimum_z+a))
        hl = np.maximum(hl_inf, hl_z)
        hu = np.minimum(hu_inf, hu_z)
        lo = (np.log(vlo)[None, :]+np.where(hl>=0,c_hi,c_lo)[:,None]*hl[:,None])/math.log(3)
        hi = (np.log(vlo+vw)[None, :]+np.where(hu>=0,c_lo,c_hi)[:,None]*hu[:,None])/math.log(3)
        valid = good&(lo+inset<hi-inset)
        lower.extend((lo+inset)[valid])
        upper.extend((hi-inset)[valid])
    return not modular_gaps(lower, upper)


def make_runs(numerators):
    runs=[]
    for n in sorted(numerators):
        if runs and n==runs[-1][1]+1:
            runs[-1][1]=n
        else:
            runs.append([n,n])
    return runs


def select_t_cover(runs, endpoint_depth=9, minimum_endpoint=20/243):
    denominator=3**endpoint_depth
    endpoints=[int(round(x*denominator)) for x in prefixes(endpoint_depth)
               if x>=minimum_endpoint-1e-12]
    intervals=[]
    for start,end in runs:
        for p in endpoints:
            lo=(2*start-1)*p/(4000*denominator)
            hi=(2*end+1)*p/(4000*denominator)
            if lo<3 and hi>1:
                intervals.append((lo,hi,p,start,end))
    intervals.sort()
    current=1.;cursor=0;selected=[];gaps=[]
    while current<3:
        best=None
        while cursor<len(intervals) and intervals[cursor][0]<=current:
            if best is None or intervals[cursor][1]>best[1]:
                best=intervals[cursor]
            cursor+=1
        if best is None or best[1]<=current:
            if cursor==len(intervals):
                gaps.append([current,3.]);break
            gaps.append([current,min(3.,intervals[cursor][0])])
            current=intervals[cursor][0]
            continue
        selected.append(best)
        current=best[1]
    return selected,gaps


if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument("--m",type=int,required=True)
    parser.add_argument("--height",type=int,default=3)
    args=parser.parse_args()
    data=json.loads(Path("work/alln20261020_coefficient_cover.json").read_text())
    candidates=[r["center"][0] for r in data["coefficients"]]
    started=time.monotonic();passed=[]
    for i,n in enumerate(candidates):
        if good_cell(n,3**args.m*20/243,args.height):
            passed.append(n)
        if i%1000==0:
            print(args.m,args.height,i,len(passed),round(time.monotonic()-started,2),flush=True)
    runs=make_runs(passed)
    cover,gaps=select_t_cover(runs)
    result=dict(status="floating discovery only",minimum_m=args.m,height=args.height,
                minimum_endpoint="20/243",passed_cells=len(passed),runs=runs,
                t_cover=cover,gaps=gaps,elapsed_seconds=time.monotonic()-started)
    Path(f"work/alln20261020_finite_z_m{args.m}_h{args.height}.json").write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ("runs","t_cover")}),flush=True)
