"""Independent verification: rational polynomial root, reverse IFS, full trie.

Does not import the producing program or trust its numerical margins.
The all-shell reduction is checked separately by n5_parent_verify.py.
"""
from fractions import Fraction as F
from pathlib import Path
import json

root = Path(__file__).parent
source = json.loads((root/'fullseparation20261020_n5_joint_periodic_certificate.json').read_text())
lo = F('0.26999925640309133388080461073396780010')
hi = F('0.26999925640309133388080461073396780011')
assert F(269999,1000000) < lo < hi < F(270001,1000000)

def add(a,b):
    c=[0]*max(len(a),len(b))
    for i,v in enumerate(a):c[i]+=v
    for i,v in enumerate(b):c[i]+=v
    return c

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def power(a,n):
    out=[1]
    for _ in range(n):out=mul(out,a)
    return out

def evaluate(a,t):
    out=F(0)
    for v in reversed(a):out=t*out+v
    return out

upoly=add(mul([1,0,-1],[1,0,1,0,0,0,1]),[0]*12+[1])
vpoly=add(mul([1,0,-1],[1,1,0,0,0,0,0,1,0,0,1]),[0]*12+[1])
ypoly=add([1,1],mul([0,0,-1],vpoly))
polynomial=add(add(power(upoly,5),power(ypoly,5)),[-x for x in power([1,1],5)])
assert evaluate(polynomial,lo)>0>evaluate(polynomial,hi)

def address(word,t,tail):
    for digit in word[::-1]:tail=t*tail+(1-t)*int(digit)
    return tail

wx,wv=source['target_words']
assert wx=='101000100000' and wv=='110000010010'
for t in [lo,hi]:
    assert address(wx,t,1/(1+t))==evaluate(upoly,t)/(1+t)
    assert address(wv,t,1/(1+t))==evaluate(vpoly,t)/(1+t)

tree={}
smallest=None
for row in source['excluded']+[{'xword':wx,'vword':wv,'sign':'target'}]:
    w,v=row['xword'],row['vword']
    assert len(w)==len(v) and w[0]==v[0]=='1'
    node=tree
    for pair in zip(w[1:],v[1:]):
        assert 'leaf' not in node
        node=node.setdefault(''.join(pair),{})
    assert not node
    node['leaf']=row['sign']
    if row['sign']=='target':continue
    if row['sign']=='+':
        margin=address(w,hi,F(0))**5+(1-hi**2*address(v,hi,F(1)))**5-1
    else:
        assert row['sign']=='-'
        margin=1-address(w,lo,F(1))**5-(1-lo**2*address(v,lo,F(0)))**5
    assert margin>0
    smallest=margin if smallest is None else min(smallest,margin)

def complete(node):
    if 'leaf' in node:
        assert len(node)==1
        return 1
    assert set(node)=={'00','01','10','11'}
    return sum(complete(v) for v in node.values())

assert complete(tree)==55 and len(source['excluded'])==54
x0=address(wx,hi,F(0));x1=address(wx,lo,F(1))
v0=address(wv,hi,F(0));v1=address(wv,lo,F(1))
s0=lo**2*((1-hi**2*v1)/x1)**4
s1=hi**2*((1-lo**2*v0)/x0)**4
b=1-hi-hi**2
assert s0-hi**2/b>F('0.03527449')
assert b-s1>F('0.51088531')
assert 2*(1-hi**2)**5>1
assert s0>F('0.1462157132262') and s1<F('0.1462158321275')

# Independent interval estimates for nonemptiness throughout the wider J5.
jlo=F(269999,1000000);jhi=F(270001,1000000)
assert F(78,100)**5+F(933,1000)**5<1
assert F(8,10)**5+F(927,1000)**5>1
assert 1-jhi**2>F(927,1000)
assert 1-jlo**2+jhi**4<F(933,1000)
derivative_lower=jlo*(F(927,1000)/F(8,10))**4
derivative_upper=jhi*(F(933,1000)/F(78,100))**4
assert derivative_lower>1-2*jlo
assert derivative_upper<jlo/(1-2*jlo)
assert derivative_upper<1-jhi
assert (1-jhi)+jlo**2>F(8,10)
assert ((1-jlo)*(1+jhi**2))**5+(1-jlo**2)**5<1

out={'status':'PASS','scope':'Exactly four points at the specified algebraic n=5 parameter, conditional only on separately verified all-shell reduction; wide-window nonempty inequalities also checked.',
     'lambda_bracket':[str(lo),str(hi)],'root_polynomial_coefficients_low_to_high':polynomial,
     'leaf_count':55,'excluded':54,'max_word_length':max(len(x['xword']) for x in source['excluded']),
     'minimum_strict_leaf_margin_decimal':float(smallest),'slope_bounds_decimal':[float(s0),float(s1)],
     'wide_window_nonempty_derivative_bounds':[float(derivative_lower),float(derivative_upper)],
     'proof_checks':['Upper address parameter derivatives in [-1,0] give strict residual monotonicity.',
     'Reverse IFS endpoints independently checked on a wider decimal bracket.',
     'Complete four-child trie, no missing or duplicated leaves.',
     'Periodic same-sign differences avoid the slope interval; equal cylinder depths preserve slope.',
     'Graph between two roots remains inside their rectangle; mean value theorem applies.']}
(root/'fullseparation20261020_n5_joint_parent_verify.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:v for k,v in out.items() if k not in ['root_polynomial_coefficients_low_to_high','proof_checks']},indent=2))
