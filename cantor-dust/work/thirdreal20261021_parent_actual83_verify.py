"""Exact actual-curve source for n=8/3; no asymptotic transfer."""
from fractions import Fraction as F
from pathlib import Path
import json
P,p,Q,q=1349417288366350224,38,5541340632044816,35
r=F(5621659580810688002470561,3884026733719813895964984)
def cube_root_bounds(value):
 scale=10**100;lo=0;hi=2*scale;target=value.numerator*scale**3
 assert target<hi**3*value.denominator
 while hi-lo>1:
  mid=(lo+hi)//2
  if mid**3*value.denominator<target:lo=mid
  else:hi=mid
 return F(lo,scale),F(hi,scale)
for v,d in [(P,p),(Q,q)]:
 assert 0<v<3**d
 for _ in range(d):v,digit=divmod(v,3);assert digit in (0,2)
 assert v==0
x=F(P,3**p);y=F(Q,3**q);hx=F(1,3**p);hy=F(1,3**q);n=F(8,3)
ax,bx=cube_root_bounds(x**5);ay,by=cube_root_bounds(y**5)
Ax,Bx=cube_root_bounds((x+hx)**5);Ay,By=cube_root_bounds((y+hy)**5)
numerator_lo=1-x*bx-y*by;numerator_hi=1-x*ax-y*ay
assert 0<numerator_lo<numerator_hi
Tlo=numerator_lo/(2*n*by*hy);Thi=numerator_hi/(2*n*ay*hy)
assert r/3<Tlo<Thi<(r+3)/6
error_x=max(abs(ax*hx/(by*hy)-r),abs(Bx*hx/(ay*hy)-r))/2
error_y=By/(2*ay)-F(1,2)
tolerance=F(1,10**7)/(2*3**17)
assert error_x+error_y<tolerance
# Strict independent algebraic crossing as another consistency check.
def below_one(x,y):
 A=x**8;B=y**8
 return A+B<1 and (1-A-B)**3>27*A*B
assert below_one(x,y) and not below_one(x+hx,y+hy)
out={'status':'PASS','method':'100-decimal-place exact rational cube-root enclosures, exact gradient bounds on full Cantor rectangle','P':P,'p':p,'Q':Q,'q':q,'slope':str(r),'level_bounds':[str(Tlo),str(Thi)],'gradient_error_bound':str(error_x+error_y),'permitted_error':str(tolerance),'margin':'1/10000000','return_depth':17,'dimension_lower_bound':'log(2)/(17log(3))'}
Path('work/thirdreal20261021_parent_actual83_verified.json').write_text(json.dumps(out,indent=2))
print('ACTUAL8/3source PASS','T',float(Tlo),float(Thi),'Lip',float(error_x+error_y),'tolerance',float(tolerance))
