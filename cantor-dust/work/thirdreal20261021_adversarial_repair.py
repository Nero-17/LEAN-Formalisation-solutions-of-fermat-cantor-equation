from pathlib import Path
from fractions import Fraction as F
from math import gcd
import json,sys

root=Path('work')
max_exponent=int(sys.argv[1]) if len(sys.argv)>1 else 100
original=json.loads((root/f'thirdreal20261021_rational_scan_{max_exponent}.json').read_text())
repair=json.loads((root/f'thirdreal20261021_rational_repaired_{max_exponent}.json').read_text())
bands=[(F(11,9),F(2027,1624)),(F(89,73),F(171,137)),(F(101,79),F(183,143)),(F(89,57),F(171,89)),(F(143,61),F(237,101)),(F(137,57),F(219,89))]
bands += [(1/upper,1/lower) for lower,upper in bands.copy()]
def legal(value):
    depth=0
    while value:
        value,digit=divmod(value,3);depth+=1
        assert digit in (0,2)
    return depth

repaired=set()
for a,b,p,q,j,band_index in repair['individual_sources']:
    assert (a,b) not in repaired and gcd(a,b)==1
    repaired.add((a,b))
    p_depth,q_depth=legal(p),legal(q)
    assert p_depth and q_depth
    lower,upper=bands[band_index]
    assert lower<F(a*q,b*(p+1)) and F(a*(q+1),b*p)<upper
    left=b**b;right=a**b
    if j>=0:left*=3**j
    else:right*=3**(-j)
    assert left*p**a<right*(q+1)**b and left*(p+1)**a>right*q**b
    d_numerator=j+a*p_depth-b*q_depth
    k_residue=(-d_numerator*pow(a,-1,b))%b
    assert (a*k_residue+d_numerator)%b==0
remaining=set(map(tuple,repair['missing']))
assert len(remaining)==len(repair['missing'])
assert not remaining&repaired
assert remaining|repaired==set(map(tuple,original['missing']))
result={'status':'PASS','maximum_exponent':max_exponent,'repaired':len(repaired),'remaining':sorted(remaining,key=lambda v:F(*v)),'smallest_remaining':str(min(F(*v) for v in remaining)),'new_positive_interval':['1','24/23']}
output_name='thirdreal20261021_adversarial_repair_verified.json' if max_exponent==100 else f'thirdreal20261021_adversarial_repair_{max_exponent}_verified.json'
(root/output_name).write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2))
