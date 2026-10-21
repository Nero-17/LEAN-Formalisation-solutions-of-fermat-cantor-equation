"""Independent logarithmic-source verification by integer interval arithmetic.

Unlike the agent's atanh/range-two routine, this uses
  -log(1-z)=sum_{k=1}^K z^k/k + positive tail
with 0<=z<=2/3. Each operation is rounded outwards on a 2^256 lattice.
The tail is bounded by 3*(2/3)^(K+1)/(K+1).
No floating arithmetic enters any acceptance decision.
"""
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as F
import json
import hashlib
import time
import argparse

DEN = 2**256
TERMS = 256
BANDS = [(F(11,9),F(2027,1624)),(F(11,7),F(21,11)),
         (F(89,73),F(171,137)),(F(101,79),F(183,143)),
         (F(89,57),F(171,89)),(F(143,61),F(237,101)),
         (F(137,57),F(219,89))]
BANDS += [(1/b,1/a) for a,b in BANDS.copy()]
def ceiling(num,den): return -((-num)//den)
TAIL = ceiling(DEN*3*2**(TERMS+1), (TERMS+1)*3**(TERMS+1))

@lru_cache(maxsize=100000)
def log_unit(numerator,denominator):
    """Return integer lower/upper bounds for DEN*log(numerator/denominator)."""
    assert 0 < numerator <= denominator <= 3*numerator
    zlo=DEN*(denominator-numerator)//denominator
    zhi=ceiling(DEN*(denominator-numerator),denominator)
    powerlo=powerhi=DEN
    sumlo=sumhi=0
    for k in range(1,TERMS+1):
        powerlo=powerlo*zlo//DEN
        powerhi=ceiling(powerhi*zhi,DEN)
        sumlo+=powerlo//k
        sumhi+=ceiling(powerhi,k)
    return -sumhi-TAIL,-sumlo

LOG3=tuple(-v for v in reversed(log_unit(1,3)))

def log_integer(n,m):
    """Exact n logarithm; nearby integer blocks accelerate large finite lists."""
    if n<50000:
        inverse_t=log_unit(3**m,n)
        return m*LOG3[0]-inverse_t[1],m*LOG3[1]-inverse_t[0]
    base=max(3**m,(n//1000)*1000)
    assert base<=n and n-base<1000
    base_inverse=log_unit(3**m,base)
    # log(n/base)=-log(1-z), z=(n-base)/n<1/50.
    zlo=DEN*(n-base)//n
    zhi=ceiling(DEN*(n-base),n)
    assert 50*(n-base)<n
    powerlo=powerhi=DEN
    sumlo=sumhi=0
    for k in range(1,33):
        powerlo=powerlo*zlo//DEN
        powerhi=ceiling(powerhi*zhi,DEN)
        sumlo+=powerlo//k
        sumhi+=ceiling(powerhi,k)
    tail=ceiling(2*DEN,33*50**33)
    return (m*LOG3[0]-base_inverse[1]+sumlo,
            m*LOG3[1]-base_inverse[0]+sumhi+tail)

def verify(row):
    n,P,p,Q,q,d=(row[k] for k in ("n","P","p","Q","q","d"))
    assert n>=3 and d>=0
    for value,depth in ((P,p),(Q,q)):
        assert 0<value<3**depth
        for _ in range(depth):
            assert value%3 in (0,2)
            value//=3
        assert value==0
    lowratio,highratio=F(n*Q,P+1),F(n*(Q+1),P)
    band=next(((a,b) for a,b in BANDS if a<lowratio<=highratio<b),None)
    assert band is not None
    m=0
    while 3**(m+1)<=n: m+=1
    logn=log_integer(n,m)
    log_u_min=log_unit(P,3**p)
    log_u_max=log_unit(P+1,3**p)
    log_v_min=log_unit(Q,3**q)
    log_v_max=log_unit(Q+1,3**q)
    minimum_corner_upper=n*log_u_min[1]-log_v_max[0]-logn[0]+d*LOG3[1]
    maximum_corner_lower=n*log_u_max[0]-log_v_min[1]-logn[1]+d*LOG3[0]
    assert minimum_corner_upper<0<maximum_corner_lower
    return min(-minimum_corner_upper,maximum_corner_lower)

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--input",default="work/alln20261020_parent_logsource_candidates.json")
    parser.add_argument("--output",default="work/alln20261020_parent_exact_logs.json")
    args=parser.parse_args()
    raw=Path(args.input).read_bytes()
    payload=json.loads(raw)
    rows=payload["rows"]
    started=time.monotonic()
    checked=[]
    margin=None
    for i,row in enumerate(rows):
        local=verify(row)
        margin=local if margin is None else min(margin,local)
        checked.append(row["n"])
        if (i+1)%1000==0: print("verified",i+1,"seconds",time.monotonic()-started,flush=True)
    assert len(set(checked))==len(checked)
    missing=sorted(set(range(min(checked),max(checked)+1))-set(checked))
    result=dict(status="PASS",method="independent fixed-point directed integer interval log Taylor series",
                input=args.input,input_sha256=hashlib.sha256(raw).hexdigest(),
                checked=len(checked),range=[min(checked),max(checked)],missing=missing,
                lattice_denominator_bits=256,series_terms=TERMS,
                log_integer_block_terms=32,
                uniform_corner_margin_lower=str(F(margin,DEN)),
                seconds=time.monotonic()-started,
                scope="Strict log sources in proved elementary or graph bands; use the established near-axis transfer and FLT.")
    Path(args.output).write_text(json.dumps(result,indent=2))
    print(json.dumps(result,indent=2))
