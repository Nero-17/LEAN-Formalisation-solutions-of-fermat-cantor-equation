"""Independent exact-root audit of the parent's ACTUAL n=8/3 source."""
from fractions import Fraction as F
import json

def cube_enclosure(value):
    scale=10**90;low,high=0,2*scale
    target=value.numerator*scale**3
    assert high**3*value.denominator>target
    while high-low>1:
        middle=(low+high)//2
        if middle**3*value.denominator<=target:low=middle
        else:high=middle
    assert low**3*value.denominator<=target<high**3*value.denominator
    return F(low,scale),F(high,scale)

record=json.load(open('work/thirdreal20261021_parent_actual83_retry.json'))[0]
source=record['source'];certificate=record['certificate']
P,p,Q,q=(source[key] for key in ('P','p','Q','q'))
x,y,wx,wy=F(P,3**p),F(Q,3**q),F(1,3**p),F(1,3**q)
n=F(8,3);r=F(record['rational_slope'])
xl,xh=cube_enclosure(x**5);yl,yh=cube_enclosure(y**5)
xrl,xrh=cube_enclosure((x+wx)**5);yrl,yrh=cube_enclosure((y+wy)**5)
numerator_lower=1-x*xh-y*yh
numerator_upper=1-x*xl-y*yl
assert numerator_lower>0
level_lower=numerator_lower/(2*n*yh*wy)
level_upper=numerator_upper/(2*n*yl*wy)
assert r/3<level_lower<level_upper<(r+3)/6
normalized_x_lower=(wx/wy)*xl/yh
normalized_x_upper=(wx/wy)*xrh/yl
x_derivative_error=max(abs(normalized_x_lower-r),abs(normalized_x_upper-r))/2
y_derivative_error=(yrh/yl-1)/2
lipschitz=x_derivative_error+y_derivative_error
permitted=F(certificate['margin'])/(2*3**certificate['depth'])
assert lipschitz<permitted
for prefix,depth in ((P,p),(Q,q)):
    for _ in range(depth):
        prefix,digit=divmod(prefix,3)
        assert digit in (0,2)
    assert prefix==0
out={'status':'INDEPENDENT EXACT ACTUAL n=8/3 SOURCE PASS','P':P,'p':p,'Q':Q,'q':q,
     'r':str(r),'return_margin':certificate['margin'],'return_depth':certificate['depth'],
     'level_bounds':[str(level_lower),str(level_upper)],'lipschitz_bound':str(lipschitz),
     'permitted_lipschitz':str(permitted),'root_precision':90,
     'normalization':'(x^n+y^n-1)/(2*n*y_left^(n-1)*3^(-q))',
     'dimension_lower_bound':'log(2)/(17*log(3))'}
json.dump(out,open('work/thirdreal20261021_irrational_83_actual_verified.json','w'),indent=2)
print(out['status'],'level',float(level_lower),'Lip',float(lipschitz),'permitted',float(permitted))
