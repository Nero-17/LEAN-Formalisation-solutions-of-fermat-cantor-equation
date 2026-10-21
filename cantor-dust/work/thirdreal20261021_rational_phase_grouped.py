from thirdreal20261021_rational_phase_certificate import *

def grouped(m,D,h,uniform=False,step=100):
 from thirdreal20261021_rational_uniform_probe import intervals as uniform_intervals
 from thirdreal20261021_rational_finite_probe import finite_intervals
 from alln20261020_inner_phase_probe import modular_gaps
 float_intervals=uniform_intervals if uniform else finite_intervals
 recent=[p for p in prefixes(D)if p>0];v=Verifier(m,D,h,uniform=uniform);stack=[(F(i,step),F(i+1,step),0)for i in range(3*step-1,step-1,-1)];cells=[];fail=[];start=time.time()
 tag=f'tail_m{m}'if uniform else f'fixed_m{m}'
 while stack:
  lo,hi,level=stack.pop();remaining=set(range(2,110));groups=[]
  for P in recent:
   ll,uu=float_intervals(float(lo),float(hi),m,P,D,h)
   maybe=[b for b in sorted(remaining)if not modular_gaps(b*ll,b*uu)]
   if not maybe:continue
   exactintervals,total=v.intervals(P,lo,hi)
   okay=[b for b in maybe if modular_cover(exactintervals,total,b)]
   if okay:groups.append([P,okay]);remaining-=set(okay)
   if not remaining:break
  if not remaining:
   cells.append([str(lo),str(hi),groups]);chosen=[p for p,_ in groups];recent=chosen+[p for p in recent if p not in chosen]
  elif level<12:
   mid=(lo+hi)/2;stack.extend([(mid,hi,level+1),(lo,mid,level+1)])
  else:fail.append([str(lo),str(hi),sorted(remaining)])
  if len(cells)%100==0 and not remaining:print('progress',tag,len(cells),len(stack),len(fail),round(time.time()-start,1),flush=True)
  if len(fail)>10:break
  if len(cells)%500==0 and not remaining:
   Path(f'work/thirdreal20261021_rational_grouped_{tag}.json').write_text(json.dumps({'status':'PARTIAL','m':m,'D':D,'h':h,'uniform':uniform,'cells':cells,'failures':fail,'remaining_stack':len(stack)},separators=(',',':')))
 out={'status':'PASS'if not fail and not stack else'INCOMPLETE','m':m,'D':D,'h':h,'uniform':uniform,'denominators':[2,109],'cells':cells,'failures':fail,'remaining_stack':len(stack),'seconds':time.time()-start}
 Path(f'work/thirdreal20261021_rational_grouped_{tag}.json').write_text(json.dumps(out,separators=(',',':')))
 print('DONE',tag,out['status'],len(cells),fail[:10],round(time.time()-start,1),flush=True)
if __name__=='__main__':
 if sys.argv[1]=='tail':grouped(9,8,1,True)
 else:
  m=int(sys.argv[1]);grouped(m,m-1,1)
