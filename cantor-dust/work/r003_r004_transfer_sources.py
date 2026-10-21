"""Deep actual Fermat cylinders for a fixed-slope R004 return certificate."""
from fractions import Fraction as F
from pathlib import Path
import json

def state(n,P,p,Q,q):
    factor=3**(n*(q-p))
    target=3**(n*q)
    defect=target-Q**n-factor*P**n
    denominator=2*n*factor*P**(n-1)
    slope=F(Q**(n-1),factor*P**(n-1))
    intercept=F(defect,denominator)
    lipschitz=F((Q+1)**(n-1)-Q**(n-1),2*factor*P**(n-1))+F(
        (P+1)**(n-1)-P**(n-1),2*P**(n-1))
    switch=[(F(1,3),(slope+1)/6),(slope/3,(slope+3)/6),
            ((slope+1)/3,(3*slope+1)/6)]
    return dict(n=n,P=P,p=p,Q=Q,q=q,slope=str(slope),intercept=str(intercept),
                lipschitz=str(lipschitz),slope_decimal=float(slope),
                intercept_decimal=float(intercept),
                switch_margin=str(max(min(intercept-a,b-intercept) for a,b in switch)),
                lower_defect=str(-defect),
                upper_defect=str((Q+1)**n+factor*(P+1)**n-target))

def deepen(n,P,p,Q,q,minimum=35,maximum=90):
    factor=3**(n*(q-p))
    for depth in range(maximum+1):
        current=state(n,P,p+depth,Q,q+depth)
        if depth>=minimum and F(current["switch_margin"])>F(1,10000):
            current["additional_depth"]=depth
            return current
        candidates=[]
        for i in (0,2):
          for j in (0,2):
            PP,QQ=3*P+i,3*Q+j
            target=3**(n*(q+depth+1))
            if QQ**n+factor*PP**n<target<(QQ+1)**n+factor*(PP+1)**n:
                child=state(n,PP,p+depth+1,QQ,q+depth+1)
                r,t=F(child["slope"]),F(child["intercept"])
                candidates.append((min(t,(r+1)/2-t),PP,QQ))
        assert candidates
        _,P,Q=max(candidates)
    return dict(n=n,status="no_deep_switch_source")

if __name__=="__main__":
    results=[deepen(9,708,7,14348844,15),deepen(10,2132,8,129139992,17)]
    for row in results:
        print({k:v for k,v in row.items() if k in
               ("n","P","p","Q","q","slope_decimal","intercept_decimal","additional_depth")})
    Path("work/r003_r004_transfer_sources.json").write_text(json.dumps(results,indent=2))
