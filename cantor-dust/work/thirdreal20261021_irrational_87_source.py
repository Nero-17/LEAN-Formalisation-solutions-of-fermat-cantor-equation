"""Exact dyadic-branch geometry for n=8/7, phase j=2; decimal diagnostics."""
import sys
sys.dont_write_bytecode=True
import json
from decimal import Decimal as D,getcontext
getcontext().prec=85

def crosses(P,Q,depth):
    scale=3**depth
    return (9*7**7*P**8 < 8**7*(Q+1)**7*scale and
            9*7**7*(P+1)**8 > 8**7*Q**7*scale)

def children(P,Q,depth):
    return [(3*P+a,3*Q+b) for a in (0,2) for b in (0,2) if crosses(3*P+a,3*Q+b,depth+1)]

if __name__=='__main__':
    nodes=[(2,2)];output=[]
    for depth in range(1,46):
        following=[]
        for P,Q in nodes:
            cc=children(P,Q,depth)
            if depth>=40 and len(cc)>=2:
                scale=D(3)**depth;u=D(P)/scale;v=D(Q)/scale
                A=D(8)/7/D(9)**(D(1)/7)
                r=(9*u)**(D(1)/7)
                # Reflected v source, normalized L=(r*s+t)/2.
                level=(A*(v+1/scale)-u**(D(8)/7))/(2*A/scale)
                output.append({'P':P,'Q':Q,'depth':depth,'r':str(r),'level':str(level),
                               'children':cc,'u':str(u),'v':str(v)})
            following+=cc
        nodes=[(P,Q) for P,Q in following
               if (9*(P+1)/3**(depth+1))**(1/7)>1.315 and
                  (9*P/3**(depth+1))**(1/7)<1.325]
        # Preserve a wide deterministic beam if finite scan grows.
        if len(nodes)>300:nodes=[nodes[round(i*(len(nodes)-1)/299)] for i in range(300)]
        if len(output)>=10:break
    if len(output)>20:output=[output[round(i*(len(output)-1)/19)] for i in range(20)]
    open('work/thirdreal20261021_irrational_87_sources.json','w').write(json.dumps(output,indent=2))
    for row in output:print(row['depth'],row['P'],row['Q'],row['r'][:22],row['level'][:22])
