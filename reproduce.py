#!/usr/bin/env python3
"""Reproduce exact certificate checks in a disposable local workspace."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parent
SPECIAL = (9, 10, 23, 25, 28, 31, 32, 78, 82)
GENERATED_REPORTS = {
    'r008_evidence_gap_family.json', 'continuity20261020_low_n3_certificate.json',
    'r003_r004_transfer_verification.json', 'r003_parent_finite_coverage.json',
    'r010_parent_weighted_verify_57_50.json', 'alln20261020_all_integer_coverage.json',
    'alln20261020_finite_z_m15_depth11_verified.json', 'alln20261020_parent_finite_m15_verified.json',
    *(f'r003_parent_antichain_verify_n{n}.json' for n in SPECIAL),
    *(f'alln20261020_fixed_m{m}_{side}_verified.json' for m in (12,13,14) for side in ('lower','upper')),
    *(f'alln20261020_parent_{part}_verified.json' for part in ('complete_301_10000','10001_50000','50001_177146','177147_531440')),
}

def jobs(suite):
    quick = [
        ('polynomial-gaps', ['work/r008_evidence_gap_family.py']),
        ('cubic-exclusion', ['work/continuity20261020_low_n3_certificate.py']),
        ('quartic-exclusion', ['work/separation20261020_parent_check.py']),
        ('digital-graphs', ['work/r003_digits_verify.py']),
    ]
    returns = [(f'binary-return-{n}', ['work/r003_parent_antichain_verify.py', '--n', str(n), '--compact']) for n in SPECIAL]
    returns += [('source-transfer-9-10', ['work/r003_r004_transfer_verify.py']),
                ('small-integers', ['work/r003_parent_verify_sources.py']),
                ('weighted-circle', ['work/r010_parent_weighted_return_verify.py',
                 'work/branching_r010_adaptive_B_57_50_theta2.json', '--output', 'work/r010_parent_weighted_verify_57_50.json'])]
    integer_sources = []
    for tag, source, report in [
        ('301-10000', 'complete_301_10000', 'complete_301_10000'),
        ('10001-50000', 'parent_logsource_10001_50000', '10001_50000'),
        ('50001-177146', 'batch_50001_177146', '50001_177146'),
        ('177147-531440', 'batch_177147_531440', '177147_531440'),
    ]:
        source = 'logsource_'+source if source.startswith('complete') else source
        integer_sources.append(('integer-sources-'+tag, ['work/alln20261020_parent_exact_logs.py',
            '--input', 'work/alln20261020_'+source+'.json',
            '--output', 'work/alln20261020_parent_'+report+'_verified.json']))
    phases = [(f'fixed-scale-{m}-{side}', ['work/alln20261020_verify_fixed_m.py', '--m', str(m),
        '--input', f'work/alln20261020_fixed_m{m}_{side}_candidate.json'])
        for m in (12, 13, 14) for side in ('lower', 'upper')]
    phases += [('infinite-tail', ['work/alln20261020_verify_finite_z.py', '--m', '15', '--endpoint-depth', '11']),
               ('independent-infinite-tail', ['work/alln20261020_parent_finite_phase.py', '--m', '15', '--endpoint-depth', '11'])]
    assembly = [('coverage-assembly', ['work/alln20261020_assemble.py'])]
    groups = {'quick':quick, 'returns':returns, 'integer-sources':integer_sources, 'phase-covers':phases, 'assembly':assembly}
    prefix = 'work/thirdreal20261021_'
    def real(name, script, *arguments):
        return (name, [prefix+script+'.py', *arguments])
    groups['real-quick'] = [
        real('rational-lattice-width', 'rational_verify'),
        real('actual-8-over-3-source', 'parent_actual83_verify'),
        real('independent-8-over-3-source', 'irrational_83_actual_verify'),
    ]
    groups['real-sources'] = [real('finite-rationals', 'adversarial_scan', '2187'),
                              real('repaired-rationals', 'adversarial_repair', '2187')]
    groups['real-phase-covers'] = [real(f'real-phase-{m}', 'parent_layers', str(m)) for m in range(7,12)]
    groups['real-returns'] = [
        real('near-one-sources', 'adversarial_nearone'),
        real('near-one-returns', 'adversarial_returns'),
        real('8-over-7-source', 'adversarial_87'),
        real('8-over-7-returns', 'adversarial_returns', '3291854706059752449652/2493145389759550335983','15'),
        real('11-over-4-source-and-returns', 'adversarial_general_source'),
        real('53-over-2-source-and-returns', 'adversarial_532_verify'),
        real('independent-53-over-2-source', 'parent_532'),
        real('8-over-3-returns', 'rational_actual83_returns_verify'),
        real('8-over-3-return-comparison', 'rational_actual83_returns_compare'),
    ]
    groups['real-assembly'] = [real('retained-large-scale-joins', 'adversarial_large'),
                               real('real-coverage-ledger', 'adversarial_final')]
    groups['numerical-anchor'] = [(name, ['work/fullseparation20261020_'+script+'.py']) for name,script in
                                  [('n5-shell-reduction','n5_parent_verify'),('n5-core-exclusion','n5_joint_parent_verify')]]
    groups['uniform-bound'] = [('uniform-last-bound', ['universal-last-bound/verify_universal_bound.py', '--replay'])]
    if suite == 'uniform-bound-audit':
        return [('uniform-last-bound-saved-reports', ['universal-last-bound/verify_universal_bound.py'])]
    return sum(groups.values(), []) if suite == 'all' else groups.get(suite, [])

def materialize_uniform(workspace):
    metadata = json.loads((ROOT/'docs/supplement-manifest.json').read_text(encoding='utf-8'))
    archive = ROOT/metadata['path']
    if hashlib.sha256(archive.read_bytes()).hexdigest() != metadata['sha256']:
        raise RuntimeError('Supplement archive checksum mismatch')
    destination = workspace/'universal-last-bound'
    destination.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(archive) as packed:
        manifest = json.loads(packed.read('MANIFEST.json'))
        if set(packed.namelist()) != set(manifest)|{'MANIFEST.json'}:
            raise RuntimeError('Supplement contains missing or unlisted files')
        for name, checksum in manifest.items():
            if Path(name).name != name:
                raise RuntimeError('Unexpected supplement path: '+name)
            raw = packed.read(name)
            if hashlib.sha256(raw).hexdigest() != checksum:
                raise RuntimeError('Supplement input checksum mismatch: '+name)
            target = destination/name
            if not target.exists():
                target.write_bytes(raw)
            elif not name.endswith('_verification.json') and target.read_bytes() != raw:
                raise RuntimeError('Workspace supplement input modified: '+str(target))
        (destination/'MANIFEST.json').write_bytes(packed.read('MANIFEST.json'))
    return len(manifest)


def materialize(workspace):
    manifest = json.loads((ROOT/'docs'/'source-manifest.json').read_text())
    work = workspace/'work'
    work.mkdir(parents=True, exist_ok=True)
    for item in manifest:
        packed = ROOT/item.get('packed_path',item['path'])
        raw = gzip.decompress(packed.read_bytes()) if packed.suffix=='.gz' else packed.read_bytes()
        if hashlib.sha256(raw).hexdigest() != item['sha256']:
            raise RuntimeError('Input checksum mismatch: '+str(packed))
        target = work/Path(item['path']).name
        # Preserve reports generated by a previous stage in this workspace.
        if not target.exists():target.write_bytes(raw)
        elif target.name not in GENERATED_REPORTS and not (target.name.startswith(('thirdreal20261021_', 'fullseparation20261020_')) and (target.name.endswith('_verified.json') or target.name.endswith('_verify.json') or target.name.endswith('_final_ledger.json'))):
            if target.read_bytes()!=raw:raise RuntimeError('Workspace input modified: '+str(target))
    return manifest

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('suite', choices=['prepare','audit','quick','returns','integer-sources','phase-covers','assembly','real-quick','real-sources','real-phase-covers','real-returns','real-assembly','numerical-anchor','uniform-bound','uniform-bound-audit','all'])
    parser.add_argument('--workspace', type=Path, default=ROOT/'.reproduce')
    parser.add_argument('--only', help='Run a single job name within the selected suite')
    parser.add_argument('--list', action='store_true', help='List exact commands without running or extracting them')
    args=parser.parse_args()
    if sys.version_info < (3,11):raise SystemExit('Python 3.11 or later is required.')
    if not __debug__:raise SystemExit('Do not use python -O: the exact verifiers require assertions.')
    if args.list:
        for name, arguments in jobs(args.suite):
            print(name+': python '+' '.join(arguments))
        return
    workspace=args.workspace.resolve()
    manifest=materialize(workspace)
    supplement_count=materialize_uniform(workspace)
    if args.suite in ('prepare','audit'):
        experiments=json.loads((ROOT/'docs/experiments-manifest.json').read_text(encoding='utf-8'))
        for item in experiments:
            if hashlib.sha256((ROOT/item['path']).read_bytes()).hexdigest()!=item['sha256']:
                raise RuntimeError('Experiment/figure input checksum mismatch: '+item['path'])
        print(f'PASS: checked {len(manifest)} primary, {supplement_count} supplement and {len(experiments)} experiment/figure input hashes; no mathematical checks were rerun.')
        return
    selected=jobs(args.suite)
    if args.only:
        selected=[job for job in selected if job[0]==args.only]
        if not selected:raise SystemExit('Unknown job name for this suite.')
    logs=workspace/'logs'; logs.mkdir(exist_ok=True)
    records=[]
    for name, arguments in selected:
        start=time.time()
        print('RUN',name,flush=True)
        with (logs/(name+'.txt')).open('w',encoding='utf-8') as output:
            result=subprocess.run([sys.executable,'-X','utf8',*arguments],cwd=workspace,stdout=output,stderr=subprocess.STDOUT)
        record={'job':name,'command':['python',*arguments],'exit_code':result.returncode,'elapsed_seconds':round(time.time()-start,3),'log':'logs/'+name+'.txt'}
        records.append(record)
        (workspace/(args.suite+'-results.json')).write_text(json.dumps(records,indent=2)+'\n')
        if result.returncode:
            print((logs/(name+'.txt')).read_text(encoding='utf-8')[-6000:])
            raise SystemExit(result.returncode)
        print('PASS',name,record['elapsed_seconds'],'s',flush=True)
    print(f'PASS: {len(records)} jobs; outputs are in {workspace}',flush=True)

if __name__=='__main__':main()
