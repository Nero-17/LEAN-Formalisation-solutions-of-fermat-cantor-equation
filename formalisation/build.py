"""Verify this source distribution or build its accepted dependency graph serially.

Python 3.11+; standard library only. Historical logs are never used to skip builds.
"""
from __future__ import annotations
import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
LEAN = ROOT / 'Lean'
HISTORICAL_SHA = '9abb2c5ac39e1f7cb42e625fba3a1dc854cc1aa2cea419cc7d9bc71e0e29747a'
MATHLIB = '520045ab14e26149ee970e2e617ca04b09bde5d6'
FLAGS = subprocess.CREATE_NO_WINDOW if os.name == 'nt' else 0

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def read_json(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def verify_distribution():
    historical = ROOT / 'evidence/original-acceptance.json'
    require(digest(historical) == HISTORICAL_SHA, 'Historical acceptance bytes changed')
    report = read_json(historical)
    manifest = read_json(ROOT / 'SOURCE_MANIFEST.json')
    require(report['accepted'] and not report['gaps'], 'Historical audit is not accepted')
    require(manifest['paper_commit'] == report['paper_commit'], 'Wrong frozen manuscript')
    require(len(manifest['modules']) == 4155, 'Wrong dependency count')
    originals = {row['module']: row for row in report['modules_in_topological_order']}
    seen = set()
    for row in manifest['modules']:
        name = row['module']
        require(name not in seen and name in originals, f'Duplicate/unknown module: {name}')
        expected = originals[name]
        require(row['dependencies'] == expected['dependencies'], f'Dependency graph changed: {name}')
        require(all(x in seen for x in row['dependencies']), f'Graph is not topologically ordered: {name}')
        require(digest(LEAN / name) == row['sha256'] == expected['source_sha256'].lower(),
                f'Source bytes differ from accepted snapshot: {name}')
        require(digest(ROOT / row['historical_log']) == row['historical_log_sha256'] ==
                expected['compiler_log_sha256'].lower(), f'Historical log changed: {name}')
        seen.add(name)
    require(seen == set(originals), 'Required source is missing')
    for row in report['original_manuscript_files'] + report['external_registers']:
        require(digest(ROOT / row['path']) == row['sha256'].lower(), f'Changed audited input: {row["path"]}')
    for path, key in [('MANUSCRIPT_STATEMENTS_LATEST.json', 'inventory_sha256'),
                      ('MANUSCRIPT_DECLARATION_MAP.json', 'declaration_map_sha256'),
                      ('manuscript_acceptance.py', 'checker_sha256')]:
        require(digest(ROOT / path) == report[key].lower(), f'Changed audited input: {path}')
    print('PASS: 4,155 accepted sources, dependency graph, historical logs, manuscript and trust registers.', flush=True)
    return manifest

@contextmanager
def compile_lock():
    path = LEAN / '.publication-build.lock'
    with path.open('a+b') as handle:
        if handle.tell() == 0:
            handle.write(b'0')
            handle.flush()
        handle.seek(0)
        if os.name == 'nt':
            import msvcrt
            msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            import fcntl
            fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            yield
        finally:
            handle.seek(0)
            if os.name == 'nt':
                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                fcntl.flock(handle, fcntl.LOCK_UN)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true', help='Actually compile all accepted modules, serially')
    parser.add_argument('--check', action='store_true', help='Verify source/evidence identity only (default)')
    parser.add_argument('--module', help='Build only this .lean module and its dependencies; not full acceptance')
    parser.add_argument('--package-root', type=Path, help='Use existing pinned package caches instead of Lake environment')
    parser.add_argument('--inside-lake', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    require(not args.module or args.build, '--module requires --build')
    require(not (args.check and args.build), 'Choose --check or --build')
    if args.build and not args.inside_lake and args.package_root is None:
        lake = shutil.which('lake')
        require(lake, 'Install the pinned Lean toolchain and put lake on PATH')
        command = [lake, 'env', sys.executable, str(Path(__file__).resolve()), '--build', '--inside-lake']
        if args.module:
            command += ['--module', args.module]
        return subprocess.call(command, cwd=LEAN, creationflags=FLAGS)
    manifest = verify_distribution()
    if not args.build:
        print('Identity audit only; no new Lean compilation was run.')
        return 0
    lean = shutil.which('lean')
    require(lean, 'lean is not on PATH')
    version = subprocess.check_output([lean, '--version'], text=True, creationflags=FLAGS)
    require(re.search(r'\bversion 4\.32\.1\b', version), 'Expected Lean 4.32.1: '+version)
    env = os.environ.copy()
    paths = [str(LEAN)]
    if args.package_root:
        package_root = args.package_root.resolve()
        head = subprocess.check_output(['git', '-C', str(package_root/'mathlib'), 'rev-parse', 'HEAD'],
                                       text=True, creationflags=FLAGS).strip()
        require(head == MATHLIB, 'Existing mathlib checkout has the wrong commit')
        paths += [str(p/'.lake/build/lib/lean') for p in sorted(package_root.iterdir()) if p.is_dir()]
    else:
        head = subprocess.check_output(['git', '-C', str(LEAN/'.lake/packages/mathlib'), 'rev-parse', 'HEAD'],
                                       text=True, creationflags=FLAGS).strip()
        require(head == MATHLIB, 'Lake resolved the wrong mathlib commit')
        paths.append(env.get('LEAN_PATH', ''))
    env['LEAN_PATH'] = os.pathsep.join(paths)
    rows = {r['module']: r for r in manifest['modules']}
    selected = set(rows)
    if args.module:
        require(args.module in rows, 'Unknown module: '+args.module)
        selected = set()
        def visit(name):
            if name in selected:
                return
            selected.add(name)
            for dependency in rows[name]['dependencies']:
                visit(dependency)
        visit(args.module)
    logs = LEAN / 'build-logs'
    logs.mkdir(exist_ok=True)
    newest_sources = {}
    compiled = skipped = 0
    with compile_lock():
        for row in manifest['modules']:
            name = row['module']
            if name not in selected:
                continue
            source = LEAN / name
            artifact = source.with_suffix('.olean')
            log = logs / (name.replace('/', '_')+'.log')
            newest_sources[name] = max([source.stat().st_mtime_ns] +
                                       [newest_sources[d] for d in row['dependencies']])
            prior = log.read_text(encoding='utf-8-sig') if log.exists() else ''
            # Only this checkout's real successful log and artifact allow resumption.
            if (artifact.exists() and artifact.stat().st_size and
                artifact.stat().st_mtime_ns >= newest_sources[name] and
                'SHA256='+row['sha256'].upper() in prior and
                re.search(r'^EXIT=0\s*$', prior, re.M) and 'END_UTC=' in prior):
                skipped += 1
                continue
            started = datetime.now(timezone.utc).isoformat()
            timer = time.monotonic()
            temporary = artifact.with_suffix('.olean.building')
            with log.open('w', encoding='utf-8', newline='\n') as output:
                output.write(f'UTC={started} MODULE={name} SHA256={row["sha256"].upper()}\n')
                output.flush()
                result = subprocess.run([lean, '-j', '1', '-o', str(temporary), name], cwd=LEAN,
                                        env=env, stdout=output, stderr=subprocess.STDOUT, creationflags=FLAGS)
                output.write(f'ELAPSED_SECONDS={time.monotonic()-timer} END_UTC={datetime.now(timezone.utc).isoformat()}\nEXIT={result.returncode}\n')
            if result.returncode:
                print(f'FAILED: {name}; see {log}', file=sys.stderr)
                return result.returncode
            require(temporary.exists() and temporary.stat().st_size > 0, 'Compiler produced no artifact: '+name)
            temporary.replace(artifact)
            compiled += 1
            print(f'PASS {compiled+skipped}/{len(selected)} {name}', flush=True)
    print(f'Compilation finished: {compiled} rebuilt, {skipped} current, {len(selected)} selected.')
    if not args.module:
        return subprocess.call([sys.executable, str(ROOT/'manuscript_acceptance.py')], cwd=ROOT, creationflags=FLAGS)
    print('Selected-module run only; this does not establish full-manuscript acceptance.')
    return 0

if __name__ == '__main__':
    try:
        sys.exit(main())
    except (RuntimeError, OSError, ValueError) as error:
        print('ERROR:', error, file=sys.stderr)
        sys.exit(1)
