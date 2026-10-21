"""Independent replay of the exact n=5 partial reduction; never infer roots."""
from fractions import Fraction as F
from pathlib import Path
import json

root=Path(__file__).parent
data=json.loads((root/'fullseparation20261020_n5_core_reduction.json').read_text())
lam=F(27,100)
assert F(data['contraction'])==lam and data['exponent']==5
assert 5*(1-lam)*(1-lam**5)>1
assert 5*lam**3<(1-lam)**5

def hull(word):
    lower=F(0)
    width=F(1)
    for bit in word:
        if bit=='1':lower+=(1-lam)*width
        width*=lam
    return lower,lower+width

def quotient(t):
    return sum(((1-t)**i for i in range(5)),F(0))

summaries=[]
complete_case_margins=[]
for case in data['cases']:
    d=case['phase']; t0,t1=map(F,case['scale'])
    tree={}
    for kind in ['excluded','remaining']:
        for row in case[kind]:
            xw,vw=row['xword'],row['vword']
            assert len(xw)==len(vw) and xw[0]==vw[0]=='1'
            node=tree
            for pair in zip(xw[1:],vw[1:]):
                assert 'leaf' not in node
                node=node.setdefault(''.join(pair),{})
            assert not node
            node['leaf']=kind
            if kind=='remaining':continue
            x0,x1=hull(xw);v0,v1=hull(vw)
            sign=row['sign']
            if sign=='+':margin=x0**5-lam**d*v1*quotient(t0*v1)
            elif sign=='-':margin=lam**d*v0*quotient(t1*v0)-x1**5
            else:
                assert sign=='order' and t0==t1
                margin=x0+t0*v0-1
            assert margin>0 and margin==F(row['margin'])
            if len(summaries)<3:complete_case_margins.append(margin)
    def complete(node):
        if 'leaf' in node:
            assert len(node)==1
        else:
            assert set(node)=={'00','01','10','11'}
            for child in node.values():complete(child)
    complete(tree)
    summaries.append({'phase':d,'scale':case['scale'],
                      'excluded':len(case['excluded']),
                      'unresolved':len(case['remaining'])})
assert [v['unresolved'] for v in summaries[:3]]==[0,0,0]
assert len(data['cases'])==4 and summaries[-1]['unresolved']>0
upper=F(270001,1000000)
assert 1-2*upper**5>0
assert 5*(1-upper)*(1-upper**5)>1
assert (1-upper)**5-5*upper**3>0
# Independent parameter Lipschitz proof, rather than replaying interval arithmetic.
# Upper-cylinder endpoint derivatives are in [-1,0], Q5<=5, |Q5'|<=10.
for d,p in [(1,1),(1,6),(2,7)]:
    b=F(7,25)
    bound=5+5*d*b**(d-1)+5*b**d+10*b**d*(p*b**(p-1)+b**p)
    assert bound<15
assert min(complete_case_margins)>F(15,1000000)
result={'status':'PASS_PARTIAL_REDUCTION','cases':summaries,
        'uniform_lambda_interval':['269999/1000000','270001/1000000'],
        'independent_lipschitz_margin':str(min(complete_case_margins)-F(15,1000000)),
        'scope':'Only core k=0,m=2 remains; no existence or dimension of that core is proved.'}
(root/'fullseparation20261020_n5_parent_verify.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
