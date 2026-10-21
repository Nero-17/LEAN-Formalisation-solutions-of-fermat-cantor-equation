"""Independent reconstruction of the limiting coefficient phase certificate.

Logarithms come from directed integer -log(1-z) series, not the agent's
atanh series. Circle coverage is checked with integer endpoint events.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
import time
from alln20261020_parent_exact_logs import DEN, LOG3, log_unit, ceiling

SCALE = 2**100
POSITION = 2*3**7
PERIOD = SCALE*4000*POSITION
BANDS = [(F(11,9),F(2027,1624)),(F(11,7),F(21,11))]
BANDS += [(1/b,1/a) for a,b in BANDS.copy()]

@lru_cache(None)
def prefixes(depth):
    if depth == 0:
        return (0,)
    return tuple(3*a+d for a in prefixes(depth-1) for d in (0,2))

RECIP = (SCALE*DEN//LOG3[1], ceiling(SCALE*DEN,LOG3[0]))
LOGS = {}
for q in prefixes(4):
    for v in (162+q,163+q):
        low,high = log_unit(v,243)
        LOGS[v] = (SCALE*low//LOG3[0], ceiling(SCALE*high,LOG3[1]))

def product_bounds(coefficient_low,coefficient_high):
    values=(coefficient_low*RECIP[0],coefficient_low*RECIP[1],
            coefficient_high*RECIP[0],coefficient_high*RECIP[1])
    return min(values),max(values)

def verify_cell(k):
    events={}
    center=27*POSITION//2
    inset=ceiling(PERIOD,10**12)
    for depth in range(5,11):
        step=2*3**(10-depth)
        denominator=4000*3**(depth-3)
        for tail in prefixes(4):
            v=162+tail
            lo,hi=F((2*k-1)*v,denominator),F((2*k+1)*(v+1),denominator)
            if not any(a<lo and hi<b for a,b in BANDS):
                continue
            for a in prefixes(depth):
                al=a*step
                dl=center-al-step
                du=center-al
                lower=LOGS[v][1]*4000*POSITION+product_bounds((2*k-1)*dl,(2*k+1)*dl)[1]+inset
                upper=LOGS[v+1][0]*4000*POSITION+product_bounds((2*k-1)*du,(2*k+1)*du)[0]-inset
                if lower>=upper:
                    continue
                assert upper-lower<PERIOD
                shift=lower//PERIOD
                lower-=shift*PERIOD
                upper-=shift*PERIOD
                segments=[(lower,min(upper,PERIOD))]
                if upper>PERIOD:
                    segments.append((0,upper-PERIOD))
                for left,right in segments:
                    events[left]=events.get(left,0)+1
                    events[right]=events.get(right,0)-1
    active=0
    previous=0
    for position,change in sorted(events.items()):
        assert active>0 or position==previous,("gap",k,previous,position)
        active+=change
        previous=position
    assert previous==PERIOD and active==0

if __name__=="__main__":
    started=time.monotonic()
    path=Path("work/alln20261020_selected_cover.json")
    data=json.loads(path.read_text())
    assert data["endpoint_depth"]==9 and data["height"]==3 and data["v_depth"]==4
    cells=sorted({k for lo,hi in data["selected_runs"] for k in range(lo,hi+1)})
    for i,k in enumerate(cells):
        verify_cell(k)
        if (i+1)%500==0:
            print("verified",i+1,"of",len(cells),flush=True)
    intervals=[]
    for row in data["t_cover"]:
        p=row["P"]
        assert p>0 and p in prefixes(9)
        lo,hi=row["run"]
        assert [lo,hi] in data["selected_runs"]
        intervals.append((F((2*lo-1)*p,4000*3**9),F((2*hi+1)*p,4000*3**9)))
    right=F(1)
    for lo,hi in sorted(intervals):
        assert lo<=right
        right=max(right,hi)
    assert right>=3
    result=dict(status="PASS",method="independent integer log series and endpoint-event union",
                coefficient_cells=len(cells),t_intervals=len(intervals),
                input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                seconds=time.monotonic()-started)
    Path("work/alln20261020_parent_phase_verified.json").write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
