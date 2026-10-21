from pathlib import Path
from fractions import Fraction as F
from bisect import bisect_right
from math import gcd
import json,time,sys
from functools import lru_cache

started=time.monotonic()
root=Path('work');max_exponent=int(sys.argv[1]) if len(sys.argv)>1 else 100
data=json.loads((root/f'thirdreal20261021_rational_scan_{max_exponent}.json').read_text())
bands=[(F(11,9),F(2027,1624)),(F(89,73),F(171,137)),(F(101,79),F(183,143)),(F(89,57),F(171,89)),(F(143,61),F(237,101)),(F(137,57),F(219,89))]
bands += [(1/upper,1/lower) for lower,upper in bands.copy()]
def legal(value):
    assert value>0
    depth=0
    while value:
        value,digit=divmod(value,3);depth+=1
        if digit not in (0,2):return None
    return depth

sources={}; reconstructed=[]
S=1<<200
def ceiling(numerator,denominator):return -((-numerator)//denominator)
def unit_log(x,y):
    assert 0<=3*x<=y
    zlo=S*x//y;zhi=ceiling(S*x,y)
    z2lo=zlo*zlo//S;z2hi=ceiling(zhi*zhi,S)
    lower=upper=0
    # Horner evaluation, independent from the producer's successive powers.
    for j in range(69,-1,-1):
        lower=S//(2*j+1)+z2lo*lower//S
        upper=ceiling(S,2*j+1)+ceiling(z2hi*upper,S)
    tail=ceiling(3*S,141*3**141)
    return 2*(zlo*lower//S),2*ceiling(zhi*upper,S)+tail
log_two=unit_log(1,3)
@lru_cache(None)
def integer_log(value):
    assert value>=1
    exponent=value.bit_length()-1;power=1<<exponent
    lower,upper=unit_log(value-power,value+power)
    return exponent*log_two[0]+lower,exponent*log_two[1]+upper
def linear_log(terms):
    lower=upper=0
    for coefficient,integer in terms:
        lo,hi=integer_log(integer)
        lower+=coefficient*(lo if coefficient>=0 else hi)
        upper+=coefficient*(hi if coefficient>=0 else lo)
    return lower,upper

for index,(a,b,p,q,j,band_index) in enumerate(data['individual_sources']):
    assert 2<=b<=109 and b<a<max_exponent*b and gcd(a,b)==1
    assert (a,b) not in sources
    p_depth,q_depth=legal(p),legal(q)
    assert p_depth and q_depth
    lower,upper=bands[band_index]
    assert lower<F(a*q,b*(p+1)) and F(a*(q+1),b*p)<upper
    if max_exponent==100:
        left_factor=b**b;right_factor=a**b
        if j>=0:left_factor*=3**j
        else:right_factor*=3**(-j)
        assert left_factor*p**a<right_factor*(q+1)**b
        assert left_factor*(p+1)**a>right_factor*q**b
    else:
        negative=linear_log([(j,3),(b,b),(a,p),(-b,a),(-b,q+1)])
        positive=linear_log([(j,3),(b,b),(a,p+1),(-b,a),(-b,q)])
        assert negative[1]<0 and positive[0]>0,(a,b,p,q,j)
    # Physical source phase: b*d-a*p_depth+b*q_depth=j.
    phase_numerator=j+a*p_depth-b*q_depth
    residue=(-phase_numerator*pow(a,-1,b))%b
    assert (a*residue+phase_numerator)%b==0
    sources[(a,b)]=True
    if index<3:reconstructed.append({'a':a,'b':b,'p_depth':p_depth,'q_depth':q_depth,'d':str(F(phase_numerator,b)),'k_residue_mod_b':residue})
    if index and index%5000==0:print('Exact source checks',index,flush=True)

missing=set(map(tuple,data['missing']))
assert len(missing)==len(data['missing'])
assert not (missing & set(sources))
assert all(2<=b<=109 and b<a<max_exponent*b and gcd(a,b)==1 for a,b in missing)

integers=[0]
for _ in range(7):integers=[3*p+d for p in integers for d in (0,2)]
integers=integers[1:]
rows=[]
for p in integers:
    for q in integers:
        for lower,upper in bands:
            left=lower*F(p+1,q);right=upper*F(p,q+1)
            if left<right and right>1 and left<3:rows.append((left,right,p,q))

total=0;width_count=0;source_count=0;missing_count=0
for b in range(2,110):
    intervals=[]
    for lower,upper,p,q in rows:
        lower=max(lower,(F(11,10*b)-F(1,q+1))*(p+1))
        if lower<upper and upper>1 and lower<3:intervals.append((lower,upper))
    merged=[]
    for lower,upper in sorted(intervals):
        if merged and lower<merged[-1][1]:merged[-1]=(merged[-1][0],max(upper,merged[-1][1]))
        else:merged.append((lower,upper))
    starts=[lower for lower,upper in merged]
    for a in range(b+1,max_exponent*b):
        if gcd(a,b)!=1:continue
        total+=1;scale=1
        while a>=3*b*scale:scale*=3
        normalized=F(a,b*scale)
        index=bisect_right(starts,normalized)-1
        in_width=index>=0 and merged[index][0]<normalized<merged[index][1]
        in_source=(a,b) in sources
        in_missing=(a,b) in missing
        assert sum((in_width,in_source,in_missing))==1,(a,b,in_width,in_source,in_missing)
        width_count+=in_width;source_count+=in_source;missing_count+=in_missing
assert (total,width_count,source_count,missing_count)==(data['total'],data['lattice_width_covered'],len(sources),len(missing))
result={'status':'PASS','maximum_exponent':max_exponent,'total':total,'width_covered':width_count,'exact_sources':source_count,'unresolved_by_this_scan':missing_count,'source_sign_method':'Integer powers' if max_exponent==100 else 'Independent 200-bit 70-term outward Horner logarithms','source_phase_reconstruction_examples':reconstructed,'seconds':time.monotonic()-started}
output_name='thirdreal20261021_adversarial_scan_verified.json' if max_exponent==100 else f'thirdreal20261021_adversarial_scan_{max_exponent}_verified.json'
(root/output_name).write_text(json.dumps(result,indent=2))
print(json.dumps(result,indent=2),flush=True)
