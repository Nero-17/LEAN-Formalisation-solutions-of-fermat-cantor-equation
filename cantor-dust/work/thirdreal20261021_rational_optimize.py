exec(open('work/thirdreal20261021_rational_latticecover.py').read().split('for qmax')[0])
rows=[]
for P in ints:
 for Q in ints:
  for a,b in bands:
   lo=a*F(P+1,Q);hi=b*F(P,Q+1)
   if lo<hi and hi>1 and lo<3:rows.append((lo,hi,P,Q,a,b))
def cover(B):
 viable=[]
 for lo,hi,P,Q,a,b in rows:
  lo=max(lo,(F(11,10*B)-F(1,Q+1))*(P+1))
  if lo<hi:viable.append((lo,hi,P,Q,a,b))
 edge=F(1);chosen=[]
 while edge<=3:
  good=[r for r in viable if r[0]<edge<r[1]]
  if not good:return None
  best=max(good,key=lambda r:r[1]);chosen.append(best);edge=best[1]
 return chosen
l,h=1,266
while h-l>1:
 mid=(l+h)//2
 if cover(mid):h=mid
 else:l=mid
chosen=cover(h)
print('CUT',h,len(chosen))
data=[{'lo':str(r[0]),'hi':str(r[1]),'P':r[2],'Q':r[3],'slope_lo':str(r[4]),'slope_hi':str(r[5])} for r in chosen]
Path('work/thirdreal20261021_rational_latticecover_optimized.json').write_text(json.dumps({'denominator':h,'rows':data},indent=2))
print(data)
