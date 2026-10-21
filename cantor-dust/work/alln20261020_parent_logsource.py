"""Floating discovery of logarithmic Fermat sources at finite exponents.

Uses legal ternary cylinders around several positive endpoints. Every returned
row still needs rational interval verification of the logarithms and slopes.
"""
from pathlib import Path
import numpy as np
import math
import json
import argparse
import time

BANDS = [(11/9, 2027/1624), (11/7, 21/11),
         (89/73,171/137),(101/79,183/143),(89/57,171/89),
         (143/61,237/101),(137/57,219/89)]
BANDS += [(1/b, 1/a) for a,b in BANDS.copy()]
PREF = {0: np.array([0], dtype=np.int64)}
def prefixes(depth):
    if depth not in PREF:
        old=prefixes(depth-1)
        PREF[depth]=np.sort(np.r_[3*old,3*old+2])
    return PREF[depth]

def find_source(n, max_q=6):
    m=0
    while 3**(m+1)<=n: m+=1
    # Low-depth endpoints make the perturbation legal even at n=301.
    for endpoint_depth in (2,3,1,4,5,6):
        if endpoint_depth>m: continue
        endpoints=prefixes(endpoint_depth)
        endpoints=endpoints[endpoints>=2*3**(endpoint_depth-1)]
        for height in (min(2,m-endpoint_depth), min(3,m-endpoint_depth), 0):
            for q in range(2,max_q+1):
                V=2*3**(q-1)+prefixes(q-1)
                v0=V/3.**q
                v1=(V+1)/3.**q
                for da in range(max(0,q+height-2),q+height+3):
                    p=m-height+da
                    if p<endpoint_depth: continue
                    A=prefixes(da)
                    for endpoint in endpoints:
                        U=int(endpoint)*3**(p-endpoint_depth)+A
                        u0=U[:,None]/3.**p
                        u1=(U[:,None]+1)/3.**p
                        factor=n*3.**(q-p)
                        rlow=factor*v0[None,:]/u1
                        rhigh=factor*v1[None,:]/u0
                        good=np.zeros(rlow.shape,dtype=bool)
                        for lo,hi in BANDS:
                            good|=(rlow>lo+1e-10)&(rhigh<hi-1e-10)
                        if not good.any(): continue
                        lower=(n*np.log(u0)-np.log(v1)[None,:]-math.log(n))/math.log(3)
                        upper=(n*np.log(u1)-np.log(v0)[None,:]-math.log(n))/math.log(3)
                        integer=np.floor(lower)+1
                        good&=(integer<upper-1e-10)
                        if good.any():
                            ai,vi=np.argwhere(good)[0]
                            band=next([lo,hi] for lo,hi in BANDS if rlow[ai,vi]>lo and rhigh[ai,vi]<hi)
                            return dict(n=n,m=m,P=int(U[ai]),p=p,Q=int(V[vi]),q=q,
                                d=int(-integer[ai,vi]),band=band,
                                lower_margin=float(integer[ai,vi]-lower[ai,vi]),
                                upper_margin=float(upper[ai,vi]-integer[ai,vi]),
                                normal_bounds=[float(rlow[ai,vi]),float(rhigh[ai,vi])],
                                endpoint=int(endpoint),endpoint_depth=endpoint_depth,height=height,
                                status="floating_discovery_only")
    return None

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--start",type=int,default=301)
    parser.add_argument("--end",type=int,default=2000)
    parser.add_argument("--missing-only",action="store_true")
    parser.add_argument("--max-q",type=int,default=5)
    parser.add_argument("--output",default="work/alln20261020_parent_logsource_candidates.json")
    args=parser.parse_args()
    ns=list(range(args.start,args.end+1))
    if args.missing_only:
        prior=json.loads(Path("work/alln20261020_interval_probe_dense.json").read_text())
        ns=[row["n"] for row in prior if not row["found"]]
    started=time.monotonic()
    rows=[]
    missing=[]
    for i,n in enumerate(ns):
        result=find_source(n,args.max_q)
        if result is None: missing.append(n)
        else: rows.append(result)
        if i%5000==0 or i+1==len(ns):
            output=dict(scope="floating discovery only",tested=i+1,total=len(ns),found=len(rows),
                        missing=missing,seconds=time.monotonic()-started,rows=rows)
            Path(args.output).write_text(json.dumps(output,indent=2))
            print({k:v for k,v in output.items() if k!="rows"},flush=True)
