"""Exact prefix-tree exploration; decimal slopes select later exact certificates."""
import sys
sys.dont_write_bytecode=True
import json,argparse
from decimal import Decimal as D,getcontext
getcontext().prec=85

def source_candidates(a,b,j,depth_target=40,beam=350):
    def crosses(P,Q,depth):
        factor=3**(depth*(a-b))
        return b**b*3**j*P**a < a**b*(Q+1)**b*factor and b**b*3**j*(P+1)**a > a**b*Q**b*factor
    def children(P,Q,depth):
        return [(3*P+c,3*Q+d) for c in (0,2) for d in (0,2) if crosses(3*P+c,3*Q+d,depth+1)]
    nodes=[(2,2)];output=[]
    for depth in range(1,depth_target+1):
        following=[]
        for P,Q in nodes:
            cc=children(P,Q,depth)
            if depth==depth_target and len(cc)>=2:
                scale=D(3)**depth;u=D(P)/scale;v=D(Q)/scale
                r=(D(3)**j*u**(a-b))**(D(1)/b)
                level=(v+1/scale-D(b)/a*r*u)/(2/scale)
                output.append({'a':a,'b':b,'j':j,'P':P,'Q':Q,'depth':depth,'r':str(r),'level':str(level),'children':cc})
            following+=cc
        nodes=following
        if len(nodes)>beam:nodes=[nodes[round(i*(len(nodes)-1)/(beam-1))] for i in range(beam)]
    if len(output)>25:output=[output[round(i*(len(output)-1)/24)] for i in range(25)]
    return output

if __name__=='__main__':
    for a,b,j in [(13,12,3),(19,18,4),(24,23,5)]:
        rows=source_candidates(a,b,j)
        open(f'work/thirdreal20261021_irrational_{a}_{b}_sources.json','w').write(json.dumps(rows,indent=2))
        print(a,b,j,len(rows),[(x['r'][:16],x['level'][:12]) for x in rows[::5]],flush=True)
