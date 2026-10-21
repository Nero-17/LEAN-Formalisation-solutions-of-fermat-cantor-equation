from fractions import Fraction as F
from pathlib import Path
import json,time
from thirdreal20261021_irrational_scalar_bounded import check
rows=json.loads(Path('work/thirdreal20261021_parent_actual83_sources.json').read_text())
rows.sort(key=lambda r:min(abs(float(r['r'])-v)for v in [1.45,2.138,1.32]))
seen=set();out=[]
for row in rows:
 r=F(row['r']).limit_denominator(10**25);key=round(float(r),5)
 if key in seen:continue
 seen.add(key);start=time.time();cert=check(r,22,2500000,margin=F(1,10**7))
 out.append({'source':row,'rational_slope':str(r),'certificate':cert})
 print('actual83retry',float(r),cert['complete'],cert['depth'],round(time.time()-start,2),flush=True)
 Path('work/thirdreal20261021_parent_actual83_retry.json').write_text(json.dumps(out,indent=2))
 if cert['complete']:break
