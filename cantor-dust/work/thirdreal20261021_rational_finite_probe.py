from alln20261020_fixed_m_phase import *
def finite_intervals(tlo,thi,m,P,D,h,depth=4):
 lower=[];upper=[]
 for rlo,rhi,pl,pu,lv,uv in geometry(m,P,D,h,depth):
  good=np.zeros_like(rlo,dtype=bool)
  for lo,hi in BANDS:good|=(tlo*rlo>lo)&(thi*rhi<hi)
  left=(lv+np.where(pl>=0,thi,tlo)*pl)/math.log(3)+1e-9;right=(uv+np.where(pu>=0,tlo,thi)*pu)/math.log(3)-1e-9
  good&=left<right;lower.extend(left[good]);upper.extend(right[good])
 return np.array(lower),np.array(upper)
if __name__=='__main__':
 start=time.monotonic();out=[]
 for m in [6,7,8]:
  D=m-1;endpoints=[int(round(x*3**D))for x in prefixes(D)if x>0];recent=endpoints.copy()
  for t in np.linspace(1,3,41):
   found=None
   for P in recent:
    ll,uu=finite_intervals(float(t),float(t),m,P,D,1)
    if all(not modular_gaps(b*ll,b*uu)for b in range(2,110)):found=P;break
   if found:recent.remove(found);recent.insert(0,found)
   out.append({'m':m,'D':D,'h':1,'t':float(t),'found':found})
   print(m,round(float(t),3),found,round(time.monotonic()-start,1),flush=True)
  Path('work/thirdreal20261021_rational_finite_probe.json').write_text(json.dumps(out,indent=2))
