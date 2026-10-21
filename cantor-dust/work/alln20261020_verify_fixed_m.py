"""Exact verification of fixed-M full-phase parameter cells.

All numerical discovery endpoints are discarded. Only integer prefixes,
depths and rational parameter endpoints are used.
"""
from pathlib import Path
from fractions import Fraction as F
from bisect import bisect_left, bisect_right
from functools import lru_cache
import argparse
import hashlib
import json
import math
import time
from alln20261020_finite_phase_transfer import log_bounds

BASE=[(F(11,9),F(2027,1624)),(F(11,7),F(21,11)),
      (F(89,73),F(171,137)),(F(101,79),F(183,143)),
      (F(89,57),F(171,89)),(F(143,61),F(237,101)),
      (F(137,57),F(219,89))]
BANDS=BASE+[(1/b,1/a) for a,b in BASE]
SCALE=2**80

def floor(value):return value.numerator//value.denominator
def ceil(value):return -floor(-value)

@lru_cache(None)
def prefixes(depth):
    result=[0]
    for _ in range(depth):
        result=[3*x+d for x in result for d in (0,2)]
    return result


class Verifier:
    def __init__(self,m,endpoint_depth=6,height=3,depth=4):
        self.m=m
        self.M=3**m
        self.endpoint_depth=endpoint_depth
        self.height=height
        self.depth=depth
        assert m>=endpoint_depth+height
        self.log3=log_bounds(F(3),80)
        self.qs=[2*3**depth+b for b in prefixes(depth)]
        self.logs={}
        for q in self.qs:
            for value in (q,q+1):
                lo,hi=log_bounds(F(value,3**(depth+1)),80)
                candidates=[u/v for u in (lo,hi) for v in self.log3]
                self.logs[value]=(floor(SCALE*min(candidates)),
                                  ceil(SCALE*max(candidates)))
        self.geometry={}
        self.ps=range(max(0,depth+height-2),depth+height+4)

    def build_geometry(self,P):
        assert P in prefixes(self.endpoint_depth) and P>0
        Mu=self.M*P//3**self.endpoint_depth
        assert Mu*3**self.endpoint_depth==self.M*P
        center=F(3**self.height,2)
        h={}
        rows={}
        for p in self.ps:
            length=3**(p-self.height)
            for A in prefixes(p):
                for value in (A,A+1):
                    a=F(value,length)
                    if a not in h:
                        lo,hi=log_bounds((Mu+center)/(Mu+a),12)
                        candidates=[self.M*u/v for u in (lo,hi) for v in self.log3]
                        h[a]=(floor(SCALE*min(candidates)),ceil(SCALE*max(candidates)))
            rows[p]=[(A,h[F(A+1,length)][1],h[F(A,length)][0]) for A in prefixes(p)]
        self.geometry[P]=(Mu,rows)

    def covers_cell(self,P,tlo,thi):
        if P not in self.geometry:self.build_geometry(P)
        Mu,rows=self.geometry[P]
        denominator=math.lcm(tlo.denominator,thi.denominator)
        low=tlo.numerator*(denominator//tlo.denominator)
        high=thi.numerator*(denominator//thi.denominator)
        total_denominator=denominator*SCALE
        inset=ceil(F(total_denominator,10**12))
        intervals=[]
        for p in self.ps:
            length=3**(p-self.height)
            for q in self.qs:
                index_ranges=[]
                for blo,bhi in BANDS:
                    # Strict rlo>blo and strict rhi<bhi.
                    amax=((low*q*self.M*blo.denominator-1)//(denominator*blo.numerator)
                          -Mu*length-1)
                    amin=(high*(q+1)*self.M*bhi.denominator//(denominator*bhi.numerator)
                          -Mu*length+1)
                    start=bisect_left(prefixes(p),amin)
                    stop=bisect_right(prefixes(p),amax)
                    if start<stop:index_ranges.append((start,stop))
                if not index_ranges:continue
                merged=[]
                for start,stop in sorted(index_ranges):
                    if merged and start<=merged[-1][1]:
                        merged[-1][1]=max(merged[-1][1],stop)
                    else:merged.append([start,stop])
                for start,stop in merged:
                    for _,h_lower,h_upper in rows[p][start:stop]:
                        lower=(self.logs[q][1]*denominator+
                               (high if h_lower>=0 else low)*h_lower+inset)
                        upper=(self.logs[q+1][0]*denominator+
                               (low if h_upper>=0 else high)*h_upper-inset)
                        if lower>=upper:continue
                        shift=lower//total_denominator
                        lower-=shift*total_denominator
                        upper-=shift*total_denominator
                        intervals.append((lower,min(upper,total_denominator)))
                        if upper>total_denominator:
                            intervals.append((0,upper-total_denominator))
        intervals.sort()
        end=0
        for lower,upper in intervals:
            if lower>end:return False
            end=max(end,upper)
        return end>=total_denominator


def verify(m,input_path=None):
    started=time.monotonic()
    path=Path(input_path or f"work/alln20261020_fixed_m{m}_candidate.json")
    data=json.loads(path.read_text())
    assert data["m"]==m and not data["failures"]
    domain=tuple(map(F,data.get("parameter_domain",["1","3"])))
    assert 1<=domain[0]<domain[1]<=3
    verifiers={}
    parameter_intervals=[]
    for index,row in enumerate(data["cells"]):
        tlo,thi=F(*row["t_lower"]),F(*row["t_upper"])
        assert domain[0]<=tlo<thi<=domain[1]
        geometry=(row.get("endpoint_depth",data["endpoint_depth"]),
                  row.get("height",data["height"]),
                  row.get("v_depth",data["v_depth"]))
        if geometry not in verifiers:
            verifiers[geometry]=Verifier(m,*geometry)
        assert verifiers[geometry].covers_cell(row["P"],tlo,thi),(
            "failed exact fixed cell",index,row)
        parameter_intervals.append((tlo,thi))
        if index%100==0:
            print(m,"verified",index,"of",len(data["cells"]),
                  round(time.monotonic()-started,2),flush=True)
    end=domain[0]
    for lo,hi in sorted(parameter_intervals):
        assert lo<=end,("parameter gap",str(end),str(lo))
        end=max(end,hi)
    assert end>=domain[1]
    result=dict(verification="PASS",m=m,
                parameter_domain=list(map(str,domain)),
                integer_range=[ceil(3**m*domain[0]),
                               min(3**(m+1)-1,floor(3**m*domain[1]))],
                parameter_cells=len(data["cells"]),strict_image_inset="1/10^12",
                finite_log_terms=12,ordinary_log_terms=80,fixed_point_scale="2^80",
                geometries=[list(g) for g in verifiers],
                input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                elapsed_seconds=time.monotonic()-started,
                scope="Every real t in the reported parameter domain at this fixed M=3^m; actual nonlinear phase and assigned proved slope bands.")
    output_name=(f"alln20261020_fixed_m{m}_verified.json" if domain==(F(1),F(3))
                 else path.stem.replace("_candidate","")+"_verified.json")
    Path("work",output_name).write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--m",type=int,required=True)
    parser.add_argument("--input")
    args=parser.parse_args()
    verify(args.m,args.input)
