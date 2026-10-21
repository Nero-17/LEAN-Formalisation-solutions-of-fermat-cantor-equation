from pathlib import Path
import json,hashlib
p=Path('work/thirdreal20261021_rational_actual83_returns_verified.json')
parent=Path('work/thirdreal20261021_parent_actual83_retry.json')
actual=json.loads(p.read_text());expected=json.loads(parent.read_text())[0]['certificate']
columns=('depth','one_intervals','two_intervals','covered_components')
assert [[r[c]for c in columns]for r in actual['history']]==expected['history']
assert actual['complete'] and expected['complete'] and actual['depth']==expected['depth']==17
assert actual['margin']==expected['margin']=='1/10000000'
assert actual['lower']==actual['upper']==expected['slope']
assert actual['components']==expected['components']==[0,1,2]
actual['comparison_with_parent']='PASS: all17 depth rows match exactly, including all interval counts and covered-component counts.'
actual['parent_candidate_sha256']=hashlib.sha256(parent.read_bytes()).hexdigest()
p.write_text(json.dumps(actual,indent=2))
print(actual['comparison_with_parent']);print(actual['history'][-1])
