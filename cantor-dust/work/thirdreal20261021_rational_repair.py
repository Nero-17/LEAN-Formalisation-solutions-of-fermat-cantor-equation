from thirdreal20261021_rational_scan import *
from bisect import bisect_left,bisect_right

def find(a,b,depth=8):
 n=a/b
 pdepth=depth+int(log(n)/log(3))+2
 ps=prefixes(pdepth);qs=prefixes(depth)
 for Q in qs:
  for bi,(lf,hf) in enumerate(bands):
   lo=n*(Q+1)/float(hf);hi=n*Q/float(lf)-1
   first=bisect_right(ps,lo);last=bisect_left(ps,hi)
   if first==last:continue
   parr=np.array(ps[first:last]);low=(b*log(n*Q)-a*np.log(parr+1))/log(3);high=(b*log(n*(Q+1))-a*np.log(parr))/log(3)
   js=np.floor(low).astype(np.int64)+1
   hits=np.flatnonzero(js<high-1e-10)
   for h in hits:
    P=int(parr[h]);J=int(js[h])
    if exact(a,b,P,Q,J,bi):return [a,b,P,Q,J,bi]
 return None

if __name__=='__main__':
 maxn=int(sys.argv[1]) if len(sys.argv)>1 else 100
 from thirdreal20261021_rational_logbounds import exact_fast
 exact=exact_fast
 raw=json.loads(Path(f'work/thirdreal20261021_rational_scan_{maxn}.json').read_text());missing=raw['missing'];cert=[];start=time.time()
 for depth in [6,8,10]:
  nextmissing=[]
  for i,(a,b) in enumerate(missing):
   c=find(a,b,depth)
   if c:cert.append(c)
   else:nextmissing.append([a,b])
   if i%20==0:print(depth,i,'remaining',len(nextmissing),'seconds',round(time.time()-start,1),flush=True)
  missing=nextmissing
  print('depth',depth,'MISSING',missing,flush=True)
  Path(f'work/thirdreal20261021_rational_repaired_{maxn}.json').write_text(json.dumps({'individual_sources':cert,'missing':missing,'depth':depth,'seconds':time.time()-start},separators=(',',':')))
  if not missing:break
