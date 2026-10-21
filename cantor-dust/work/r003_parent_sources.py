"""Exact source search in both normal orientations and two proved rigidity bands."""
from fractions import Fraction
from pathlib import Path
import json, sys

bands=[(Fraction(11,9),Fraction(2027,1624)),(Fraction(5,3),Fraction(9,5))]

def prefixes(depth):
    values=[0]
    for _ in range(depth): values=[3*v+d for v in values for d in (0,2)]
    return values

def search(n,maxdifference=10,maxdepth=15):
    visited=0
    for magnitude in range(maxdifference+1):
        for difference in ([0] if magnitude==0 else [magnitude,-magnitude]):
            xp=max(0,-difference);yp=max(0,difference)
            frontier=[(P,Q) for P in prefixes(xp) for Q in prefixes(yp)]
            for common in range(maxdepth+1):
                p=xp+common;q=yp+common
                xfactor=3**(n*max(q-p,0));yfactor=3**(n*max(p-q,0))
                target=3**(n*max(p,q))
                nextfront=[]
                for P,Q in frontier:
                    visited+=1
                    lower=xfactor*P**n+yfactor*Q**n-target
                    upper=xfactor*(P+1)**n+yfactor*(Q+1)**n-target
                    if not lower<0<upper:continue
                    normalmin=Fraction(yfactor*Q**(n-1),xfactor*(P+1)**(n-1))
                    normalmax=Fraction(yfactor*(Q+1)**(n-1),xfactor*P**(n-1)) if P else None
                    possible=False
                    for band in bands:
                        if normalmin<band[1] and (normalmax is None or normalmax>band[0]):
                            possible=True
                        if band[0]<normalmin and normalmax is not None and normalmax<band[1]:
                            return dict(n=n,P=P,Q=Q,p=p,q=q,band=list(map(str,band)),
                                        lower_defect=lower,upper_defect=upper,
                                        normal_min=str(normalmin),normal_max=str(normalmax),
                                        normal_decimal=[float(normalmin),float(normalmax)],visited=visited)
                    if possible:nextfront.extend((3*P+i,3*Q+j) for i in(0,2) for j in(0,2))
                frontier=nextfront
                if not frontier:break
    return dict(n=n,found=False,visited=visited)

if __name__=="__main__":
    results=[]
    for n in range(2,int(sys.argv[1])+1 if len(sys.argv)>1 else 31):
        result=search(n)
        results.append(result)
        print(json.dumps(result),flush=True)
    Path(__file__).with_suffix(".json").write_text(json.dumps(results,indent=2),encoding="utf-8")
