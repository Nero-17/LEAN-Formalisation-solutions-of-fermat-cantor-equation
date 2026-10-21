from pathlib import Path
from fractions import Fraction as F
from contextlib import redirect_stdout
from r003_digits_affine_parameter_returns import run
import json,io,time

rows=json.loads(Path('work/thirdreal20261021_adversarial_532_candidates.json').read_text())
targets=[1.3,1.32,1.28496,1.25623,1.2533,2.1387]
rows=sorted((row for row in rows if not row['swap']),key=lambda row:min(abs(float(row['r'])-t) for t in targets))
seen=set();results=[]
for source in rows:
    bucket=round(float(source['r']),6)
    if bucket in seen:continue
    seen.add(bucket)
    slope=F(source['r']).limit_denominator(10**22)
    with redirect_stdout(io.StringIO()):
        result=run(slope,slope,F(1,100000),22,limit=500000)
    result['source']=source;results.append(result)
    Path('work/thirdreal20261021_adversarial_532_returns.json').write_text(json.dumps(results,indent=2))
    print(str(slope),result['complete'],result['depth'],flush=True)
    if result['complete']:break
    if len(results)>=20:break
