from fractions import Fraction as F
from pathlib import Path
import json
P=105672039117920552328;Q=8521470282198373850;p=42;q=40
r=F(20562225398716419716957,9622098440443747992932)
for v,d in [(P,p),(Q,q)]:
 assert 0<v<3**d
 for _ in range(d):v,digit=divmod(v,3);assert digit in (0,2)
 assert v==0
u=F(P,3**p);step=F(1,3**p)
assert (r-F(1,10**35))**2<27*u**51<(r+F(1,10**35))**2
assert (r-F(1,10**16))**2<27*u**51
assert 27*(u+step)**51<(r+F(1,10**16))**2
low=(Q+1-F(2,53)*P*(r+F(1,10**35)))/2
high=(Q+1-F(2,53)*P*(r-F(1,10**35)))/2
k=101;m=2680
assert F(m)-F(53,2)*k==F(7,2)
err0=F(51,8)*F(3)**(q-m);err1=F(51,4)*F(3)**(-m)
assert F(1,3)<low-err0<high+err0<(r+1)/6
assert F(1,2*10**16)+err1<F(1,100000)/(2*3**16)
record=json.loads(Path('work/thirdreal20261021_adversarial_532_returns.json').read_text())[0]
assert record['complete'] and record['depth']==16 and F(record['lower'])==r
# Independently reconstruct returns with the third scalar implementation.
from thirdreal20261021_irrational_scalar_bounded import check
result=check(r,16,2000000)
assert result['complete'] and result['depth']==16
out={'status':'PASS','source':'Fresh exact rational square inequalities and explicit actual-Fermat Taylor bounds','returns':'Third scalar streaming-union implementation, depth16','a':53,'b':2,'P':P,'Q':Q,'p':p,'q':q,'k':k,'m':m,'level_interval':[str(low),str(high)],'dimension_lower_bound':'log(2)/(16log(3))'}
Path('work/thirdreal20261021_parent_532_verified.json').write_text(json.dumps(out,indent=2));print('Parent53/2 PASS',float(low),float(high),flush=True)
