"""Independent finite-scale circle reconstruction, using integer Taylor logs."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import json
import time
from alln20261020_parent_phase import prefixes, BANDS
from alln20261020_parent_exact_logs import DEN, LOG3, log_unit, ceiling

SCALE=2**100
PERIOD=4000*SCALE
INSET=ceiling(PERIOD,10**12)

def log_ratio(n,d):
    if n<=d:
        return log_unit(n,d)
    lo,hi=log_unit(d,n)
    return -hi,-lo

def normalized_bounds(n,d,multiplier=1):
    logs=log_ratio(n,d)
    candidates=[F(multiplier*x,y) for x in logs for y in LOG3]
    low,high=min(candidates),max(candidates)
    return low,high

def floor_scaled(x):
    return (x*SCALE).numerator//(x*SCALE).denominator

def ceil_scaled(x):
    y=x*SCALE
    return ceiling(y.numerator,y.denominator)

def prepare(m):
    z=20*3**(m-5)
    qs=[162+b for b in prefixes(4)]
    logs={}
    for q in qs:
        for v in (q,q+1):
            lo,hi=normalized_bounds(v,243)
            logs[v]=(floor_scaled(lo),ceil_scaled(hi))
    endpoints={}
    geometries={}
    for p in range(5,11):
        length=3**(p-3)
        rows=[]
        for a in prefixes(p):
            for value in (a,a+1):
                argument=F(value,length)
                if argument not in endpoints:
                    ratio=(z+F(27,2))/(z+argument)
                    finite=normalized_bounds(ratio.numerator,ratio.denominator,z)
                    limiting=[F(27,2)-argument]
                    limiting=[v*DEN/l for v in limiting for l in LOG3]
                    endpoints[argument]=(floor_scaled(min(*finite,*limiting)),
                                         ceil_scaled(max(*finite,*limiting)))
            rows.append((a,endpoints[F(a+1,length)][1],endpoints[F(a,length)][0]))
        geometries[p]=rows
    return z,qs,logs,geometries

def check(k,z,qs,logs,geometries):
    events={}
    for p,rows in geometries.items():
        length=3**(p-3)
        for q in qs:
            cutoff=-1
            for lower_band,upper_band in BANDS:
                if F((2*k+1)*(q+1),4000*length)>=upper_band:
                    continue
                bound=F((2*k-1)*q*z,4000)/lower_band-z*length-1
                cutoff=max(cutoff,ceiling(bound.numerator,bound.denominator)-1)
            if cutoff<0:
                continue
            for a,lower_phase,upper_phase in rows:
                if a>cutoff:
                    break
                low=logs[q][1]*4000+max((2*k-1)*lower_phase,(2*k+1)*lower_phase)+INSET
                high=logs[q+1][0]*4000+min((2*k-1)*upper_phase,(2*k+1)*upper_phase)-INSET
                if low>=high:
                    continue
                assert high-low<PERIOD
                shift=low//PERIOD
                low-=shift*PERIOD
                high-=shift*PERIOD
                segments=[(low,min(high,PERIOD))]
                if high>PERIOD:
                    segments.append((0,high-PERIOD))
                for left,right in segments:
                    events[left]=events.get(left,0)+1
                    events[right]=events.get(right,0)-1
    active=0
    previous=0
    for position,change in sorted(events.items()):
        assert active>0 or position==previous,("finite phase gap",k)
        active+=change
        previous=position
    assert previous==PERIOD and active==0

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--m",type=int,required=True)
    parser.add_argument("--endpoint-depth",type=int,required=True)
    args=parser.parse_args()
    m,depth=args.m,args.endpoint_depth
    assert m>=depth+3
    suffix="" if depth==9 else f"_depth{depth}"
    path=Path(f"work/alln20261020_finite_z_m{m}_h3{suffix}.json")
    data=json.loads(path.read_text())
    assert data["height"]==3 and data["minimum_m"]==m and not data["gaps"]
    runs={(r[3],r[4]) for r in data["t_cover"]}
    cells=sorted({k for lo,hi in runs for k in range(lo,hi+1)})
    started=time.monotonic()
    geometry=prepare(m)
    for i,k in enumerate(cells):
        check(k,*geometry)
        if (i+1)%500==0:
            print("verified",i+1,"of",len(cells),flush=True)
    intervals=[]
    for row in data["t_cover"]:
        p,lo,hi=row[2:]
        assert p in prefixes(depth) and F(p,3**depth)>=F(20,243)
        intervals.append((F((2*lo-1)*p,4000*3**depth),F((2*hi+1)*p,4000*3**depth)))
    right=F(1)
    for lo,hi in sorted(intervals):
        assert lo<=right
        right=max(right,hi)
    assert right>=3
    result=dict(status="PASS",minimum_m=m,minimum_n=3**m,
                coefficient_cells=len(cells),parameter_intervals=len(intervals),
                endpoint_depth=depth,minimum_z=geometry[0],
                method="independent directed Taylor logs and integer endpoint events",
                input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                seconds=time.monotonic()-started)
    Path(f"work/alln20261020_parent_finite_m{m}_verified.json").write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
