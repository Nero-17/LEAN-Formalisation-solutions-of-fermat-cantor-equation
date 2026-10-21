from pathlib import Path
from thirdreal20261021_adversarial_general_source import verify
import json

record=next(row for row in json.loads(Path('work/thirdreal20261021_adversarial_532_returns.json').read_text()) if row['complete'])
source=record['source'];assert not source['swap']
result=verify(source['a'],source['b'],source['j'],source['P'],source['p'],source['Q'],source['q'],record)
Path('work/thirdreal20261021_adversarial_532_verified.json').write_text(json.dumps(result,indent=2))
print({k:v for k,v in result.items() if k not in ['actual_lipschitz_upper']})
