from alln20261020_fixed_m_phase import *
@lru_cache(maxsize=128)
def geometry_uniform(m,P,D,h,depth):
 M=3.**m;u=P/3.**D;center=3.**h/2;v=(2+prefixes(depth))/3;vw=3.**(-depth-1);out=[]
 for p in range(max(0,depth+h-2),depth+h+4):
  aw=3.**(h-p);a=3.**h*prefixes(p)
  rlo=aw*v[None,:]/((u+(a[:,None]+aw)/M)*vw)
  rhi=aw*(v[None,:]+vw)/(u*vw)+np.zeros((len(a),1))
  pl=M*np.log1p((center-a-aw)/(M*u+a+aw));pu=M*np.log1p((center-a)/(M*u+a))
  pl=np.maximum(pl,(center-a-aw)/u);pu=np.minimum(pu,(center-a)/u)
  out.append((rlo,rhi,pl[:,None],pu[:,None],np.log(v)[None,:],np.log(v+vw)[None,:]))
 return out

def intervals(tlo,thi,m,P,D,h,depth=4):
 lower=[];upper=[]
 for rlo,rhi,pl,pu,lv,uv in geometry_uniform(m,P,D,h,depth):
  good=np.zeros_like(rlo,dtype=bool)
  for lo,hi in BANDS:good|=(tlo*rlo>lo)&(thi*rhi<hi)
  left=(lv+np.where(pl>=0,thi,tlo)*pl)/math.log(3)+1e-9
  right=(uv+np.where(pu>=0,tlo,thi)*pu)/math.log(3)-1e-9
  good&=left<right
  lower.extend(left[good]);upper.extend(right[good])
 return np.array(lower),np.array(upper)
if __name__=='__main__':
 start=time.monotonic();out=[]
 for m in [6,7,8,9]:
  D=3;endpoints=[int(round(x*3**D))for x in prefixes(D)if x>0]
  for t in np.linspace(1,3,21):
   found=None
   for h in [1,2,3]:
    for P in endpoints:
     ll,uu=intervals(float(t),float(t),m,P,D,h)
     if all(not modular_gaps(b*ll,b*uu) for b in range(2,110)):
      found=[P,h];break
    if found:break
   out.append({'m':m,'t':float(t),'found':found})
   print(m,round(float(t),3),found,round(time.monotonic()-start,1),flush=True)
  Path('work/thirdreal20261021_rational_uniform_probe.json').write_text(json.dumps(out,indent=2))
