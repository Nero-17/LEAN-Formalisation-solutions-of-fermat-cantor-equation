"""Independent exact checks of Fermat sources and uniform nonlinear transfer."""
from fractions import Fraction
from pathlib import Path
import json
import math

def ternary(n,depth):
    result=""
    for _ in range(depth):
        result=str(n%3)+result;n//=3
    assert n==0 and set(result)<=set("02")
    return result

results=[]
for source in json.loads(Path("work/r003_r004_transfer_sources.json").read_text()):
    n,P,p,Q,q=(source[k] for k in ("n","P","p","Q","q"))
    certificate=json.loads(Path(f"work/r003_digits_compact_antichain_n{n}.json").read_text())
    slope=Fraction(Q**(n-1),3**(n*(q-p))*P**(n-1))
    intercept=Fraction(3**(n*q)-Q**n-3**(n*(q-p))*P**n,
                       2*n*3**(n*(q-p))*P**(n-1))
    lipschitz=Fraction((Q+1)**(n-1)-Q**(n-1),
                      2*3**(n*(q-p))*P**(n-1))+Fraction(
                      (P+1)**(n-1)-P**(n-1),2*P**(n-1))
    assert slope==Fraction(source["slope"])==Fraction(certificate["slope"])
    assert intercept==Fraction(source["intercept"])
    assert lipschitz==Fraction(source["lipschitz"])
    assert Q**n+3**(n*(q-p))*P**n<3**(n*q)
    assert (Q+1)**n+3**(n*(q-p))*(P+1)**n>3**(n*q)
    assert 1<slope<3
    switch=[(Fraction(1,3),(slope+1)/6),(slope/3,(slope+3)/6),
            ((slope+1)/3,(3*slope+1)/6)]
    initial_margin=max(min(intercept-a,b-intercept) for a,b in switch)
    assert initial_margin>Fraction(1,10000)
    margin=Fraction(certificate["target_margin"])
    depth=certificate["depth"]
    assert certificate["complete"]
    assert 3**depth*lipschitz<margin
    intervals=[(Fraction(int(a),int(certificate["denominator"])),
                Fraction(int(b),int(certificate["denominator"])))
               for a,b in certificate["covering_intervals"]]
    assert all(a<=b for a,b in intervals)
    assert all(intervals[i][1]<intervals[i+1][0] for i in range(len(intervals)-1))
    assert all(any(a<=u and v<=b for a,b in intervals) for u,v in switch)
    results.append(dict(n=n,verified_source_and_transfer=True,P=P,p=p,Q=Q,q=q,
                        P_ternary=ternary(P,p),Q_ternary=ternary(Q,q),
                        depth=depth,slope=str(slope),intercept=str(intercept),
                        lipschitz=str(lipschitz),amplified_lipschitz=str(3**depth*lipschitz),
                        target_margin=str(margin),initial_switch_margin=str(initial_margin),
                        dimension_bound=f"log(2)/({depth}*log(3))",
                        dimension_bound_decimal=math.log(2)/(depth*math.log(3))))
    print(n,"source and transfer verified","L",depth,
          "amplified_error",float(3**depth*lipschitz),
          "dimension",math.log(2)/(depth*math.log(3)),flush=True)
Path("work/r003_r004_transfer_verification.json").write_text(json.dumps(results,indent=2))
