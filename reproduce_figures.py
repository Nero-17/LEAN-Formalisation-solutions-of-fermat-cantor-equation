#!/usr/bin/env python3
"""Rebuild the published numerical tables and phase diagrams from archived traces.

This replays the export and plotting steps, not the expensive parameter scans.
"""
import argparse, csv, hashlib, json, shutil, subprocess, sys, time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--workspace',type=Path,default=ROOT/'.reproduce-figures')
parser.add_argument('--tables-only',action='store_true')
args=parser.parse_args()
workspace=args.workspace.resolve()
if workspace==ROOT:raise SystemExit('Choose a separate output workspace.')
manifest=json.loads((ROOT/'docs/experiments-manifest.json').read_text())
for item in manifest:
    raw=(ROOT/item['path']).read_bytes()
    assert hashlib.sha256(raw).hexdigest()==item['sha256'],item['path']
    target=workspace/item['path'];target.parent.mkdir(parents=True,exist_ok=True)
    target.write_bytes(raw)
commands=['experiments/phase-transitions/export_transition_estimates.py',
          'experiments/phase-transitions/estimate_first_transition.py']
if not args.tables_only:commands+=['figures/generate_phase_diagram.py','figures/generate_phase_diagram_zh.py']
records=[]
for script in commands:
    started=time.time()
    subprocess.run([sys.executable,'-X','utf8',str(workspace/script)],cwd=workspace,check=True)
    records.append({'script':script,'exit_code':0,'elapsed_seconds':round(time.time()-started,3)})
for name in ['first-transition-estimates.csv','phase-transition-estimates.csv']:
    with (ROOT/'figures'/name).open(newline='',encoding='utf-8') as f:expected=list(csv.DictReader(f))
    with (workspace/'figures'/name).open(newline='',encoding='utf-8') as f:actual=list(csv.DictReader(f))
    assert actual==expected,(name,'Export differs from the published table')
    assert len(actual)==25
(workspace/'results.json').write_text(json.dumps({'status':'PASS','scope':'Archived trace export and plotting; no parameter scans rerun','tables':2,'rows_per_table':25,'jobs':records},indent=2)+'\n')
print('PASS: both 25-row tables agree with the publication; output:',workspace)
