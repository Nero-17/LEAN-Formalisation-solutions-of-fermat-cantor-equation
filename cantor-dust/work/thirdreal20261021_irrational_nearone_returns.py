import sys
sys.dont_write_bytecode=True
import io,json,time
from fractions import Fraction as F
from contextlib import redirect_stdout
from r003_digits_affine_parameter_returns import run
out=[]
for a,b in [(13,12),(19,18),(24,23)]:
    rows=json.load(open(f'work/thirdreal20261021_irrational_{a}_{b}_sources.json'))
    for index in (0,12,24,6,18,3,9,15,21):
        source=rows[index];r=F(source['r']).limit_denominator(10**22);start=time.monotonic()
        with redirect_stdout(io.StringIO()):
            result=run(r,r,F(1,100000),22,limit=300000)
        result['source']=source;result['elapsed']=time.monotonic()-start;out.append(result)
        open('work/thirdreal20261021_irrational_nearone_returns.json','w').write(json.dumps(out,indent=2))
        print(a,b,index,result['complete'],result['depth'],result['history'][-1],result['elapsed'],flush=True)
        if result['complete']:break
