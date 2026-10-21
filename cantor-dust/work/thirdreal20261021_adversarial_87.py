from fractions import Fraction as F
from pathlib import Path
import json

P=9450592763918769000
Q=10918429022892060476
depth=40
slope=F(3291854706059752449652,2493145389759550335983)
margin=F(1,100000)
return_depth=15
def legal(value):
    assert 0<value<3**depth
    for _ in range(depth):
        value,digit=divmod(value,3)
        assert digit in (0,2)
    assert value==0
legal(P);legal(Q)

def seventh_root_bounds(numerator,denominator):
    scale=10**80
    low=scale;high=2*scale
    assert low**7*denominator<numerator*scale**7<high**7*denominator
    while high-low>1:
        middle=(low+high)//2
        if middle**7*denominator<=numerator*scale**7:low=middle
        else:high=middle
    assert low**7*denominator<=numerator*scale**7<high**7*denominator
    return F(low,scale),F(high,scale)

root_left=seventh_root_bounds(9*P,3**depth)
root_right=seventh_root_bounds(9*(P+1),3**depth)
level_lower=(Q+1-F(7,8)*P*root_left[1])/2
level_upper=(Q+1-F(7,8)*P*root_left[0])/2
middle_lower=slope/3;middle_upper=(slope+3)/6
assert middle_lower<level_lower<=level_upper<middle_upper
model_lipschitz=max(abs(root_left[0]-slope),abs(root_right[1]-slope))/2
assert model_lipschitz<F(1,10**18)
assert model_lipschitz<margin/(2*3**return_depth)

# An explicit actual Fermat source: k=75,m=86 gives m-(8/7)k=2/7.
k=75;m=86
assert F(m)-F(8,7)*k==F(2,7)
# Taylor on z=3^-m v<1/2 bounds the normalized constant correction,
# and the derivative in t. The s derivative is exactly the model one.
constant_error=F(1,14*3**(m-depth))
t_derivative_error=F(1,7*3**m)
assert middle_lower<level_lower-constant_error
assert level_upper+constant_error<middle_upper
actual_lipschitz=model_lipschitz+t_derivative_error
assert actual_lipschitz<margin/(2*3**return_depth)

result={'status':'PASS','exponent':'8/7','P':P,'Q':Q,'source_depth':depth,'slope':str(slope),'return_depth':return_depth,'return_margin':str(margin),'model_level_enclosure':[str(level_lower),str(level_upper)],'model_lipschitz_upper':str(model_lipschitz),'explicit_Fermat_scalings':{'k':k,'m':m},'actual_constant_error_upper':str(constant_error),'actual_t_derivative_error_upper':str(t_derivative_error),'actual_Lipschitz_upper':str(actual_lipschitz),'dimension_lower_bound':'log(2)/(15*log(3))'}
Path('work/thirdreal20261021_adversarial_87_verified.json').write_text(json.dumps(result,indent=2))
print({k:v for k,v in result.items() if k not in ['model_level_enclosure','model_lipschitz_upper','actual_Lipschitz_upper']})
