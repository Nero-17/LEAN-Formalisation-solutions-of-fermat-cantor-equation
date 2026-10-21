"""Exact finite-Z full-circle cover; integer fixed-point endpoint arithmetic.

Uses only proposed integer runs and endpoint numerators from the discovery
file. Reconstructs all phase bounds and slope tests independently.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import hashlib
import json
import time
from alln20261020_finite_phase_transfer import log_bounds

BANDS=[(F(11,9),F(2027,1624)),(F(11,7),F(21,11)),
       (F(1624,2027),F(9,11)),(F(11,21),F(7,11))]
SCALE=2**80
DENOMINATOR=4000*SCALE

def floor(value):return value.numerator//value.denominator
def ceil(value):return -floor(-value)

def prefixes(depth):
    result=[0]
    for _ in range(depth):
        result=[3*x+d for x in result for d in (0,2)]
    return result


class Verifier:
    def __init__(self, minimum_m, inset=F(1,10**12)):
        assert minimum_m>=12
        self.minimum_m=minimum_m
        self.minimum_z=20*3**(minimum_m-5)
        self.inset=ceil(DENOMINATOR*inset)
        self.log3=log_bounds(F(3),80)
        self.logs={}
        self.prefixes={p:prefixes(p) for p in range(5,11)}
        self.qs=[162+b for b in prefixes(4)]
        for q in self.qs:
            for value in (q,q+1):
                lo,hi=log_bounds(F(value,243),80)
                bounds=[u/v for u in (lo,hi) for v in self.log3]
                self.logs[value]=(floor(SCALE*min(bounds)),ceil(SCALE*max(bounds)))
        self.h={}
        for p in range(5,11):
            length=3**(p-3)
            for numerator in self.prefixes[p]:
                for value in (numerator,numerator+1):
                    argument=F(value,length)
                    if argument in self.h:continue
                    lo,hi=log_bounds(
                        (self.minimum_z+F(27,2))/(self.minimum_z+argument),10)
                    finite=[self.minimum_z*u/v for u in (lo,hi) for v in self.log3]
                    limiting=[(F(27,2)-argument)/v for v in self.log3]
                    self.h[argument]=(floor(SCALE*min(finite+limiting)),
                                      ceil(SCALE*max(finite+limiting)))
        self.rows={}
        for p in range(5,11):
            length=3**(p-3)
            self.rows[p]=[(a,self.h[F(a+1,length)][1],self.h[F(a,length)][0])
                          for a in self.prefixes[p]]

    def covers_cell(self, numerator):
        intervals=[]
        for p in range(5,11):
            length=3**(p-3)
            for q in self.qs:
                cutoff=-1
                for blo,bhi in BANDS:
                    if ((2*numerator+1)*(q+1)*bhi.denominator
                        <4000*length*bhi.numerator):
                        # Maximum allowed integer a-prefix, determined exactly.
                        lower_left=(2*numerator-1)*q*self.minimum_z*blo.denominator
                        cutoff=max(cutoff,(lower_left-1)//(4000*blo.numerator)
                                   -self.minimum_z*length-1)
                if cutoff<0:continue
                for a,h_lower,h_upper in self.rows[p]:
                    if a>cutoff:break
                    lower=(self.logs[q][1]*4000+
                           (2*numerator+(1 if h_lower>=0 else -1))*h_lower+self.inset)
                    upper=(self.logs[q+1][0]*4000+
                           (2*numerator+(-1 if h_upper>=0 else 1))*h_upper-self.inset)
                    if lower>=upper:continue
                    shift=lower//DENOMINATOR
                    lower-=shift*DENOMINATOR
                    upper-=shift*DENOMINATOR
                    intervals.append((lower,min(upper,DENOMINATOR)))
                    if upper>DENOMINATOR:
                        intervals.append((0,upper-DENOMINATOR))
        intervals.sort()
        end=0
        for lower,upper in intervals:
            if lower>end:return False
            end=max(end,upper)
        return end>=DENOMINATOR


def verify(minimum_m, endpoint_depth=9):
    started=time.monotonic()
    suffix="" if endpoint_depth==9 else f"_depth{endpoint_depth}"
    path=Path(f"work/alln20261020_finite_z_m{minimum_m}_h3{suffix}.json")
    data=json.loads(path.read_text())
    assert data["height"]==3 and data["minimum_m"]==minimum_m and not data["gaps"]
    assert endpoint_depth+3<=minimum_m
    used=sorted(set((row[3],row[4]) for row in data["t_cover"]))
    cells=sorted(set(n for lo,hi in used for n in range(lo,hi+1)))
    verifier=Verifier(minimum_m)
    for index,n in enumerate(cells):
        assert verifier.covers_cell(n),("failed finite cell",n)
        if index%500==0:
            print("verified",index,"of",len(cells),round(time.monotonic()-started,2),flush=True)
    intervals=[]
    for row in data["t_cover"]:
        p,start,end=row[2:]
        assert p in prefixes(endpoint_depth) and F(p,3**endpoint_depth)>=F(20,243)
        assert (start,end) in used
        intervals.append((F((2*start-1)*p,4000*3**endpoint_depth),
                          F((2*end+1)*p,4000*3**endpoint_depth)))
    covered=F(1)
    for lo,hi in sorted(intervals):
        assert lo<=covered,("t gap",str(covered),str(lo))
        covered=max(covered,hi)
    assert covered>=3
    result=dict(verification="PASS",minimum_m=minimum_m,minimum_n=3**minimum_m,
                minimum_z=verifier.minimum_z,minimum_endpoint="20/243",
                endpoint_depth=endpoint_depth,height=3,v_depth=4,coefficient_cells=len(cells),
                parameter_intervals=len(intervals),strict_image_inset="1/10^12",
                finite_log_terms=10,ordinary_log_terms=80,fixed_point_scale="2^80",
                input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                selected_runs=used,
                elapsed_seconds=time.monotonic()-started,
                scope="All real t in [1,3], every integer m>=minimum_m; actual finite logarithmic phase, not only its limit.")
    Path(f"work/alln20261020_finite_z_m{minimum_m}{suffix}_verified.json").write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--m",type=int,required=True)
    parser.add_argument("--endpoint-depth",type=int,default=9)
    args=parser.parse_args()
    verify(args.m,args.endpoint_depth)
