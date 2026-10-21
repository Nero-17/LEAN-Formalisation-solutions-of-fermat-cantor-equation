from pathlib import Path
from fractions import Fraction
import csv,json
base=Path(__file__).parent
def read(name):return {r['n']:r for r in map(json.loads,(base/name).read_text().splitlines())}
coarse=read('last-transition-grid.jsonl'); refined=read('last-transition-refined.jsonl')
precision=read('last-transition-precision.jsonl'); deep=read('last-transition-deep.jsonl')
assert len(deep)==25,(len(deep),'deep checks incomplete')
out=base.parent.parent/'figures'/'phase-transition-estimates.csv'
with out.open('w',newline='',encoding='utf-8') as f:
    fields=['n','estimate','coarse_last_low','refined_last_low','depth34_last_low','deep_last_low',
            'known_zero_anchor','resolution','source']
    writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
    for key in sorted(deep,key=Fraction):
        r=deep[key]; assert r['last_low'] is not None
        # A known isolated zero-dimensional parameter need not be sampled by
        # any uniform grid. Retain the explicitly documented n=5 witness.
        anchor=.2699992564030913 if key=='5' else None
        estimate=max(r['last_low'],anchor or 0.)+.00025
        writer.writerow({'n':key,'estimate':f'{estimate:.8f}',
            'coarse_last_low':coarse[key]['last_low'],'refined_last_low':refined[key]['last_low'],
            'depth34_last_low':precision[key]['last_low'],'deep_last_low':r['last_low'],
            'known_zero_anchor':anchor or '', 'resolution':.0005,
            'source':'grid and R017 isolated-zero witness' if anchor else 'finite-depth grid estimate'})
print(out)
