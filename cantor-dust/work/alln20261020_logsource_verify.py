"""Exact logarithmic source verification and local real-exponent intervals."""
import argparse
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import time

TERMS=24
BANDS=[(F(11,9),F(2027,1624)),(F(11,7),F(21,11))]
BANDS += [(1/b,1/a) for a,b in BANDS.copy()]
GRAPH_BANDS=[(F(89,73),F(171,137)),(F(101,79),F(183,143)),
             (F(89,57),F(171,89)),(F(143,61),F(237,101)),
             (F(137,57),F(219,89))]
GRAPH_BANDS += [(1/b,1/a) for a,b in GRAPH_BANDS.copy()]

def log_near_one(x):
    assert 1<=x<=2
    z=(x-1)/(x+1)
    power=z;total=F(0)
    for j in range(TERMS):
        total+=power/(2*j+1)
        power*=z*z
    remainder=2*power/((2*TERMS+1)*(1-z*z))
    return 2*total,2*total+remainder

LOG2=log_near_one(F(2))

def scale(interval,c):
    a,b=interval
    return (c*a,c*b) if c>=0 else (c*b,c*a)

@lru_cache(maxsize=50000)
def log_bounds(x):
    assert x>0
    reduced=x;power=0
    while reduced<1:reduced*=2;power-=1
    while reduced>=2:reduced/=2;power+=1
    low,high=log_near_one(reduced)
    a,b=scale(LOG2,power)
    return low+a,high+b

LOG3=log_bounds(F(3))

def ternary(prefix,depth):
    for _ in range(depth):
        assert prefix%3 in (0,2)
        prefix//=3
    assert prefix==0

def floor_rational(x,denominator=10**12):
    return F(x.numerator*denominator//x.denominator,denominator)

def corner_bounds(row,n):
    P,p,Q,q,d=(row[k] for k in ("P","p","Q","q","d"))
    u0,u1,v0,v1=F(P,3**p),F(P+1,3**p),F(Q,3**q),F(Q+1,3**q)
    ld=scale(LOG3,d);ln=log_bounds(n)
    results=[]
    for u,v in ((u0,v1),(u1,v0)):
        lu=scale(log_bounds(u),n);lv=log_bounds(v)
        results.append((ld[0]+lu[0]-lv[1]-ln[1],
                        ld[1]+lu[1]-lv[0]-ln[0]))
    return results

def verify(row,allowed_bands=None,continue_interval=True):
    n,P,p,Q,q,d=(row[k] for k in ("n","P","p","Q","q","d"))
    assert n>=3 and P>0 and Q>0
    ternary(P,p);ternary(Q,q)
    assert P+1<=3**p and Q+1<=3**q
    lower,upper=F(n*Q,P+1),F(n*(Q+1),P)
    band=next(((a,b) for a,b in (BANDS if allowed_bands is None else allowed_bands)
               if a<lower<=upper<b),None)
    assert band is not None,("normal",n)
    first,second=corner_bounds(row,F(n))
    assert first[1]<0<second[0],("corner",n,first,second)
    margins=(-first[1],second[0],lower-band[0],band[1]-upper)
    result=dict(n=n,P=P,p=p,Q=Q,q=q,d=d,band=list(map(str,band)),
        verification="PASS",normal_bounds=list(map(str,(lower,upper))),
        strict_margin_lower_bounds=[str(floor_rational(x)) for x in margins])
    if not continue_interval:
        return result
    # Continue the same source on a closed rational n interval. Each log
    # corner function has derivative log(u)-1/n<0; normals increase in n.
    # Choose the largest tested dyadic radius among 1,1/2,...,1/2^30.
    radius=F(1)
    for _ in range(31):
        nlo,nhi=F(n)-radius,F(n)+radius
        first_at_low=corner_bounds(row,nlo)[0]
        second_at_high=corner_bounds(row,nhi)[1]
        if (first_at_low[1]<0<second_at_high[0]
            and band[0]<nlo*Q/(P+1) and nhi*(Q+1)/P<band[1]):
            break
        radius/=2
    else:
        raise AssertionError(("no_uniform_radius",n))
    result["closed_real_exponent_interval"]=list(map(str,(F(n)-radius,F(n)+radius)))
    return result

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--input",default="work/alln20261020_parent_logsource_candidates.json")
    parser.add_argument("--max-n",type=int,default=2000)
    parser.add_argument("--output",default="work/alln20261020_logsource_verified.json")
    parser.add_argument("--point-only",action="store_true",
                        help="Verify integer sources without computing optional continuation intervals")
    parser.add_argument("--graph-bands",action="store_true",
                        help="Also permit the five previously proved graph bands and their reciprocals")
    args=parser.parse_args()
    for attempt in range(20):
        raw=Path(args.input).read_bytes()
        try:data=json.loads(raw);break
        except json.JSONDecodeError:
            if attempt==19:raise
            time.sleep(.05)
    source_rows=data.get("rows",data) if isinstance(data,dict) else data
    source_rows=[row for row in source_rows if row["n"]<=args.max_n]
    snapshot=Path(args.output).with_name(Path(args.output).stem+"_snapshot.json")
    snapshot.write_text(json.dumps(source_rows,indent=2))
    results=[];start=time.monotonic()
    for index,row in enumerate(source_rows):
        results.append(verify(row,allowed_bands=BANDS+GRAPH_BANDS if args.graph_bands else None,
                              continue_interval=not args.point_only))
        if (index+1)%250==0:print("VERIFIED",index+1,round(time.monotonic()-start,2),flush=True)
    report=dict(verification="PASS",count=len(results),minimum_n=min(r["n"] for r in results),
                maximum_n=max(r["n"] for r in results),atanh_terms=TERMS,
                method="binary range reduction, positive atanh series with exact geometric tail",
                snapshot_sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),
                source_file_read_sha256=hashlib.sha256(raw).hexdigest(),rows=results)
    Path(args.output).write_text(json.dumps(report,indent=2))
    print("EXACT LOG SOURCES PASS",len(results),"seconds",round(time.monotonic()-start,2))
