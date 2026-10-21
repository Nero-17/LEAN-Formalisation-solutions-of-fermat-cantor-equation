from decimal import Decimal as D,getcontext
from fractions import Fraction as F
from contextlib import redirect_stdout
import json,io,time
from r003_digits_affine_parameter_returns import run
getcontext().prec=80
out=[]
for a,b in [(8,3),(11,4),(53,2)]:
 found=[]
 for j in range(-2*b,4*b):
  def cross(P,Q,d):
   l=3**max(j,0)*b**b;r=3**max(-j,0)*a**b*3**(d*(a-b))
   return l*P**a<r*(Q+1)**b and l*(P+1)**a>r*Q**b
  if not cross(2,2,1):continue
  nodes=[(2,2)]
  for d in range(1,40):
   nxt=[]
   for P,Q in nodes:
    cc=[(3*P+x,3*Q+y) for x in (0,2) for y in (0,2) if cross(3*P+x,3*Q+y,d+1)]
    if d>=35 and len(cc)>=2:
     scale=D(3)**d;u=D(P)/scale;v=D(Q)/scale;A=D(a)/b*D(3)**(-D(j)/b)
     slope=D(a)/b*u**(D(a)/b-1)/A
     if 1<slope<3:
      level=(A*(v+1/scale)-u**(D(a)/b))/(2*A/scale)
      found.append(dict(a=a,b=b,j=j,P=P,Q=Q,depth=d,slope=str(slope),level=str(level)))
    nxt+=cc
   nodes=nxt
   if len(nodes)>30:nodes=[nodes[round(i*(len(nodes)-1)/29)] for i in range(30)]
   if len(found)>15:break
  if len(found)>15:break
 print('sources',a,b,len(found),flush=True)
 seen=set()
 for row in found:
  s=F(D(row['slope']));key=round(float(s),3)
  if key in seen:continue
  seen.add(key)
  r=F(round(s*10**20),10**20)
  with redirect_stdout(io.StringIO()):cert=run(r,r,F(1,100000),22,limit=400000)
  row['return_certificate']=cert;out.append(row)
  print(a,b,'slope',float(r),'level',row['level'][:15],'return',cert['complete'],cert['depth'],flush=True)
  open('work/thirdreal20261021_parent_model.json','w').write(json.dumps(out,indent=2))
  if cert['complete']:break
