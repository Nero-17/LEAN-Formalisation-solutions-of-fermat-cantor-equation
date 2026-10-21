import sys
sys.dont_write_bytecode=True
import io,json,time
from fractions import Fraction as F
from contextlib import redirect_stdout
from r003_digits_affine_parameter_returns import run
rows=json.load(open('work/thirdreal20261021_irrational_87_sources.json'))
out=[]
for index in (19,10,5,0):
    source=rows[index];r=F(source['r']).limit_denominator(10**22)
    for inset in ('0','1/1000','1/100'):
        start=time.monotonic()
        with redirect_stdout(io.StringIO()):
            result=run(r,r,F(1,100000),20,limit=150000,domain_inset=F(inset))
        result['source']=source;out.append(result)
        open('work/thirdreal20261021_irrational_87_return_scan.json','w').write(json.dumps(out,indent=2))
        print(index,str(r),inset,result['complete'],result['depth'],result['history'][-1],time.monotonic()-start,flush=True)
        if result['complete']:sys.exit(0)
