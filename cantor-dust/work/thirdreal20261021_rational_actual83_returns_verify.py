from fractions import Fraction as F
from pathlib import Path
import json,time,hashlib
from r003_digits_affine_parameter_returns import run
r=F(5621659580810688002470561,3884026733719813895964984)
start=time.time()
result=run(r,r,F(1,10**7),17,limit=3000000)
assert result['complete'] and result['depth']==17
assert result['components']==[0,1,2] and result['history'][-1]['covered_components']==3
result['independent_status']='PASS'
result['implementation']='Older correlated affine endpoint dynamic-programming implementation; independent from parent streaming scalar DP.'
result['elapsed_seconds']=time.time()-start
result['verifier_sha256']=hashlib.sha256(Path('work/r003_digits_affine_parameter_returns.py').read_bytes()).hexdigest()
Path('work/thirdreal20261021_rational_actual83_returns_verified.json').write_text(json.dumps(result,indent=2))
print('INDEPENDENT PASS',result['depth'],result['history'][-1],result['two_affine_sha256'],flush=True)
