"""Read-only manuscript acceptance audit; never compile or edit Lean sources.

Run: python manuscript_acceptance.py
Writes MANUSCRIPT_ACCEPTANCE.json and three exact owner-separated baseline
recheck queues. Exit 0 means every required check
accepted; exit 1 means real gaps remain. A source map or old baseline is never
substituted for current-source successful compiler evidence.
"""
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
PAPER = '429d53bb243f49b19ba8169de0e82ed70050ec7f'
INVENTORY_SHA = '480E1CDC2B95620343FDD61D4022DED475EAFF1D3524F2D93A5BD40ABB6A32FE'
ENTRY = 'LambdaCantor/Manuscript/All.lean'
DEFAULT_ROOT_ENTRY = 'LambdaCantor.lean'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
REGISTERS = ('EXTERNAL_THEOREMS.md', 'EXTERNAL_THEOREMS-R025-First.md',
             'EXTERNAL_THEOREMS-R025-LastAE.md', 'EXTERNAL_SOURCE_CHECKS-R025-Root.md')
DECL = re.compile(r'^[ \t]*(?:@\[[^\n]*\][ \t]*)?(?:(?:noncomputable|private|protected|unsafe)[ \t]+)*'
                  r'(theorem|lemma|def|abbrev|structure|inductive|axiom)[ \t]+([\w.\u0080-\uffff]+)', re.M)
NATIVE = re.compile(r'^(.+)\._native\.native_decide\.ax(?:_\d+)+$')


def digest(raw):
    return hashlib.sha256(raw).hexdigest().upper()


def utc(value):
    return datetime.fromisoformat(value.replace('Z', '+00:00'))


def strip_lean(text):
    """Erase nested comments/strings, preserving source positions and lines."""
    result, index, depth, string = [], 0, 0, False
    while index < len(text):
        pair, char = text[index:index+2], text[index]
        if depth:
            if pair == '/-': depth += 1; result.extend('  '); index += 2; continue
            if pair == '-/': depth -= 1; result.extend('  '); index += 2; continue
            result.append('\n' if char == '\n' else ' ')
        elif string:
            if char == '\\' and index+1 < len(text):
                result.extend('  '); index += 2; continue
            if char == '"': string = False
            result.append('\n' if char == '\n' else ' ')
        elif pair == '/-':
            depth = 1; result.extend('  '); index += 2; continue
        elif pair == '--':
            ending = text.find('\n', index)
            ending = len(text) if ending < 0 else ending
            result.extend(' '*(ending-index)); index = ending; continue
        elif char == '"':
            string = True; result.append(' ')
        else:
            result.append(char)
        index += 1
    if depth or string:
        raise ValueError('Unterminated Lean comment/string')
    return ''.join(result)


def local_imports(clean):
    local, packages = [], []
    for match in re.finditer(r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b([^\n]*)', clean, re.M):
        names = match[1].split()
        if not names or any(not re.fullmatch(r'[\w.]+', name) for name in names):
            raise ValueError('Unsupported import command: '+match[0])
        for name in names:
            if name == 'LambdaCantor' or name.startswith('LambdaCantor.'):
                local.append(name.replace('.', '/')+'.lean')
            else:
                packages.append(name)
    return list(dict.fromkeys(local)), list(dict.fromkeys(packages))


def qualified_declarations(text, clean=None):
    """Names of explicit axioms/native proof owners; no theorem evaluation."""
    clean, frames, entries = strip_lean(text) if clean is None else clean, [], []
    commands = re.compile(r'^[ \t]*(?:noncomputable[ \t]+)?(namespace|section|end)\b([^\n]*)|'+DECL.pattern, re.M)
    for command in commands.finditer(clean):
        if command[1]:
            kind, tail = command[1], command[2].strip()
            if kind in ('namespace', 'section'):
                frames.append((kind, tail.split()[0] if tail else ''))
            elif frames:
                frames.pop()
            continue
        # DECL's capture groups follow the command's first two groups.
        kind, name = command[3], command[4]
        namespace = '.'.join(name for frame_kind, name in frames if frame_kind == 'namespace')
        full = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(filter(None, (namespace, name)))
        entries.append({'kind': kind, 'name': full, 'start': command.start(), 'end': command.end()})
    for index, item in enumerate(entries):
        stop = entries[index+1]['start'] if index+1 < len(entries) else len(clean)
        item['native_decide_in_body'] = bool(re.search(r'\bnative_decide\b', clean[item['end']:stop]))
        item['source_line'] = clean.count('\n', 0, item['start'])+1
    return entries


def declaration_source(text, full_name):
    """Reproduce the map's LF-normalized source-signature hash convention."""
    text = text.replace('\r\n', '\n')
    name = full_name.split('.')[-1]
    matches = [item for item in DECL.finditer(text) if item[2] == name]
    if len(matches) != 1:
        raise ValueError(f'Expected one declaration {full_name}, found {len(matches)}')
    match = matches[0]
    clean = strip_lean(text)
    level, ending = 0, None
    for position in range(match.end(), len(clean)):
        char = clean[position]
        if char in '([{': level += 1
        elif char in ')]}': level -= 1
        elif level == 0 and (clean.startswith(':=', position) or re.match(r'where\b', clean[position:])):
            ending = position; break
    if ending is None:
        raise ValueError('Declaration has no proof/definition delimiter: '+full_name)
    signature = text[match.start():ending].rstrip()+'\n'
    following = next(DECL.finditer(text, match.end()), None)
    block_end = following.start() if following else len(text)
    boundary = re.search(r'^(?:end\b|namespace\b|#|/--)', text[ending:], re.M)
    if boundary:
        block_end = min(block_end, ending+boundary.start())
    block = text[match.start():block_end].rstrip()+'\n'
    statement = signature if match[1] in ('theorem', 'lemma') else block
    return {'declaration_kind': match[1], 'source_line': text.count('\n', 0, match.start())+1,
            'lean_statement_text': statement, 'lean_statement_sha256': digest(statement.encode()),
            'lean_signature_sha256': digest(signature.encode()),
            'declaration_source_sha256': digest(block.encode())}


def parse_axiom_prints(log):
    records = []
    pattern = re.compile(r"^'([^'\r\n]+)' (?:depends on axioms:\s*(\[[\s\S]*?\])|does not depend on any axioms)[ \t\r]*$", re.M)
    for match in pattern.finditer(log):
        names = [] if match[2] is None else [name.strip() for name in match[2][1:-1].split(',') if name.strip()]
        records.append({'declaration_as_printed': match[1], 'axioms_as_printed': names,
                        'raw_print_output': match[0]})
    return records


class Audit:
    def __init__(self, root):
        self.root, self.snapshots, self.modules = Path(root), {}, {}
        self.errors, self.cycles, self.ordered = [], [], []

    def read(self, path):
        path = Path(path)
        if path not in self.snapshots:
            if not path.is_file():
                self.snapshots[path] = None
            else:
                before = path.stat()
                raw = path.read_bytes()
                after = path.stat()
                self.snapshots[path] = (raw, (after.st_size, after.st_mtime_ns))
                if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
                    self.errors.append({'code': 'input_changed_during_read', 'path': str(path)})
        value = self.snapshots[path]
        return None if value is None else value[0]

    def text(self, path):
        raw = self.read(path)
        return '' if raw is None else raw.decode('utf-8-sig', errors='replace')

    def module(self, module):
        if module in self.modules:
            return self.modules[module]
        if not re.fullmatch(r'LambdaCantor(?:/[\w.-]+)*\.lean', module) or '..' in module:
            raise ValueError('Invalid project module path: '+module)
        source = self.root/'Lean'/module
        log_path = self.root/'Lean/build-logs'/(module.replace('/', '_')+'.log')
        raw, log_raw = self.read(source), self.read(log_path)
        text, log = self.text(source), self.text(log_path)
        reasons, dependencies, packages, explicit, native = [], [], [], [], []
        if raw is None:
            reasons.append('source_missing')
        else:
            try:
                clean = strip_lean(text)
                dependencies, packages = local_imports(clean)
                source_declarations = qualified_declarations(text, clean)
                explicit = [item for item in source_declarations if item['kind'] == 'axiom']
                native = [item for item in source_declarations if item['native_decide_in_body']]
                if re.search(r'\b(?:sorry|admit)\b', clean):
                    reasons.append('executable_sorry_or_admit')
            except ValueError as error:
                reasons.append('source_parser_error: '+str(error))
        headers = re.findall(r'^UTC=(\S+) MODULE=(\S+) SHA256=([0-9A-Fa-f]{64})\s*$', log, re.M)
        endings = re.findall(r'^ELAPSED_SECONDS=(\S+) END_UTC=(\S+)\s*$', log, re.M)
        exits = re.findall(r'^EXIT=(-?\d+)\s*$', log, re.M)
        if log_raw is None: reasons.append('compiler_log_missing')
        if len(headers) != 1: reasons.append('compiler_header_missing_or_ambiguous')
        if len(endings) != 1: reasons.append('compiler_end_missing_or_ambiguous')
        if len(exits) != 1: reasons.append('compiler_exit_missing_or_ambiguous')
        own_sha = digest(raw) if raw is not None else None
        if len(headers) == 1:
            if headers[0][1] != module: reasons.append('compiler_module_mismatch')
            if headers[0][2].upper() != own_sha: reasons.append('compiler_source_sha_mismatch')
        if len(exits) == 1 and exits[0] != '0': reasons.append('compiler_exit_nonzero')
        if log and (not exits or log.rstrip().splitlines()[-1] != 'EXIT=0'):
            reasons.append('compiler_log_not_completed_successfully')
        if re.search(r'(?m)^.*\berror:', log): reasons.append('compiler_error_diagnostic')
        if len(headers) == len(endings) == 1:
            try:
                if utc(endings[0][1]) < utc(headers[0][0]): reasons.append('compiler_end_precedes_start')
            except ValueError:
                reasons.append('compiler_timestamp_invalid')
        artifact = source.with_suffix('.olean')
        artifact_stat = artifact.stat() if artifact.is_file() else None
        if artifact_stat is None:
            reasons.append('olean_missing')
        record = {'module': module, 'source_sha256': own_sha,
                  'source_mtime_ns': source.stat().st_mtime_ns if raw is not None else None,
                  'canonical_log': str(log_path.relative_to(self.root)).replace('\\', '/'),
                  'compiler_log_sha256': digest(log_raw) if log_raw is not None else None,
                  'log_source_sha256': headers[0][2].upper() if len(headers) == 1 else None,
                  'log_start_utc': headers[0][0] if len(headers) == 1 else None,
                  'log_end_utc': endings[0][1] if len(endings) == 1 else None,
                  'log_exit': int(exits[0]) if len(exits) == 1 else None,
                  'olean_exists': artifact_stat is not None,
                  'olean_bytes': artifact_stat.st_size if artifact_stat else None,
                  'olean_mtime_ns': artifact_stat.st_mtime_ns if artifact_stat else None,
                  'dependencies': dependencies, 'package_imports': packages,
                  'own_current_source_exit_zero': not reasons, 'own_failures': reasons,
                  'explicit_source_axioms': explicit, 'native_proof_owners': native,
                  'axiom_prints': parse_axiom_prints(log), 'dependency_source_freshness_failures': [],
                  'later_dependency_rechecks_informational_only': []}
        self.modules[module] = record
        return record

    def closure(self, roots):
        active, visited = [], set()
        def visit(module):
            if module in active:
                self.cycles.append(active[active.index(module):]+[module]); return
            if module in visited: return
            active.append(module)
            for dependency in self.module(module)['dependencies']: visit(dependency)
            active.pop(); visited.add(module); self.ordered.append(module)
        for module in roots: visit(module)
        for module in self.ordered:
            item = self.modules[module]
            item['newest_transitive_source_mtime_ns'] = max(
                [item['source_mtime_ns'] or 0]+[self.modules[child].get('newest_transitive_source_mtime_ns', 0)
                                               for child in item['dependencies']])
            for dependency in item['dependencies']:
                child = self.modules[dependency]
                if item['olean_mtime_ns'] is not None and child.get('newest_transitive_source_mtime_ns', 0) > item['olean_mtime_ns']:
                    item['dependency_source_freshness_failures'].append({'dependency': dependency,
                        'newest_dependency_source_mtime_ns': child['newest_transitive_source_mtime_ns'],
                        'importer_olean_mtime_ns': item['olean_mtime_ns']})
                if child['log_end_utc'] and item['log_start_utc']:
                    try:
                        if utc(child['log_end_utc']) > utc(item['log_start_utc']):
                            item['later_dependency_rechecks_informational_only'].append({'dependency': dependency,
                                'dependency_end_utc': child['log_end_utc'], 'consumer_start_utc': item['log_start_utc']})
                    except ValueError:
                        pass  # Invalid timestamps already fail each module's own evidence.
            item['current_dependency_closure'] = bool(item['own_current_source_exit_zero'] and
                not item['dependency_source_freshness_failures'] and
                all(self.modules[child].get('current_dependency_closure', False) for child in item['dependencies']))

    def changed_inputs(self):
        changes = []
        for path, snapshot in self.snapshots.items():
            if snapshot is None:
                if path.exists(): changes.append(str(path))
            elif not path.is_file(): changes.append(str(path))
            else:
                stat = path.stat()
                if (stat.st_size, stat.st_mtime_ns) != snapshot[1]: changes.append(str(path))
        return changes


def registry(audit):
    allowed, registers, errors = {}, [], []
    for filename in REGISTERS:
        path, current_module = audit.root/filename, None
        raw = audit.read(path)
        if raw is None:
            errors.append({'code': 'external_registry_missing', 'path': filename}); continue
        text = audit.text(path)
        registers.append({'path': filename, 'sha256': digest(raw)})
        for line_number, line in enumerate(text.splitlines(), 1):
            module = re.search(r'(?i)\bModule:\s*`Lean/([^`]+\.lean)`', line)
            if module: current_module = module[1]
            if not re.search(r'(?i)\b(?:Declarations?|Lean axiom):', line): continue
            for span in re.findall(r'`([^`]+)`', line):
                name = span.split()[0].rstrip(':;')
                if name.startswith('Lean/') or not re.fullmatch(r'[\w.]+', name): continue
                if not name.startswith('LambdaCantor.'):
                    if current_module is None: continue
                    declarations = qualified_declarations(audit.text(audit.root/'Lean'/current_module))
                    candidates = [item['name'] for item in declarations
                                  if item['kind'] == 'axiom' and item['name'].split('.')[-1] == name]
                    if len(candidates) != 1:
                        errors.append({'code': 'ambiguous_short_registry_name', 'name': name, 'register': filename}); continue
                    name = candidates[0]
                allowed.setdefault(name, []).append({'register': filename, 'line': line_number, 'registration_line': line})
    native_text = audit.text(audit.root/'EXTERNAL_THEOREMS.md')
    native_authorized = bool('User explicitly accepted native_decide for finite certificates.' in native_text and
                             '_native.native_decide.ax' in native_text)
    return allowed, registers, errors, native_authorized


def classify_axiom(name, allowed, native_authorized, modules):
    if name == 'sorryAx' or name.endswith('.sorryAx'):
        return {'name_as_printed': name, 'category': 'forbidden_sorryAx', 'accepted': False}
    if name in STANDARD:
        return {'name_as_printed': name, 'category': 'standard', 'accepted': True}
    if name in allowed:
        matches = [{'module': item['module'], 'source_line': declaration['source_line']}
                   for item in modules.values() for declaration in item['explicit_source_axioms']
                   if declaration['name'] == name]
        return {'name_as_printed': name, 'category': 'registered_external',
                'accepted': bool(matches), 'registry_entries': allowed[name], 'source_declarations': matches}
    native = NATIVE.fullmatch(name)
    if native:
        owner = native[1]
        candidates = [{'module': item['module'], 'declaration': declaration['name'],
                       'source_line': declaration['source_line'],
                       'own_current_source_exit_zero': item['own_current_source_exit_zero']}
                      for item in modules.values() for declaration in item['native_proof_owners']
                      if declaration['name'] == owner or declaration['name'].endswith('.'+owner)]
        return {'name_as_printed': name, 'category': 'native_computation',
                'accepted': bool(native_authorized and candidates),
                'finite_native_authorization_registered': native_authorized,
                'candidate_source_owners': candidates,
                'qualification_note': 'Printed native names are retained exactly; short names can have multiple source-owner candidates.'}
    return {'name_as_printed': name, 'category': 'unregistered_axiom', 'accepted': False}


def check_default_root_entry(audit):
    root = audit.module(DEFAULT_ROOT_ENTRY)
    imports_actual_All = ENTRY in root['dependencies']
    failures = list(root['own_failures'])
    if not imports_actual_All:
        failures.append('default_root_does_not_directly_import_actual_manuscript_All')
    if not root.get('current_dependency_closure', False):
        failures.append('default_root_current_dependency_closure_not_accepted')
    return {**{key: root[key] for key in
               ('module', 'source_sha256', 'canonical_log', 'log_source_sha256', 'log_start_utc',
                'log_end_utc', 'log_exit', 'olean_exists', 'olean_bytes', 'olean_mtime_ns',
                'own_current_source_exit_zero')},
            'required_direct_import': ENTRY, 'imports_actual_manuscript_All': imports_actual_All,
            'current_dependency_closure': root.get('current_dependency_closure', False),
            'duplicates_All_axiom_prints_required': False,
            'foundations_or_old_root_artifact_is_not_a_substitute': True,
            'failures': failures, 'accepted': not failures}


def run(root=ROOT):
    started, audit = datetime.now(timezone.utc).isoformat(), Audit(root)
    checker_raw = audit.read(Path(__file__))
    gaps = []
    inventory_path = audit.root/'MANUSCRIPT_STATEMENTS_LATEST.json'
    map_path = audit.root/'MANUSCRIPT_DECLARATION_MAP.json'
    inventory_raw, map_raw = audit.read(inventory_path), audit.read(map_path)
    inventory = json.loads(inventory_raw.decode('utf-8-sig')) if inventory_raw else {}
    mapping = json.loads(map_raw.decode('utf-8-sig')) if map_raw else {}
    if inventory_raw is None or digest(inventory_raw) != INVENTORY_SHA:
        gaps.append({'code': 'fixed_original_inventory_hash_mismatch', 'expected_sha256': INVENTORY_SHA})
    if inventory.get('git_commit') != PAPER or mapping.get('paper_commit') != PAPER:
        gaps.append({'code': 'paper_commit_mismatch', 'expected': PAPER})
    inventory_rows, map_rows = inventory.get('statements', []), mapping.get('statements', [])
    if len(inventory_rows) != 34 or len(map_rows) != 34 or mapping.get('environment_count') != 34:
        gaps.append({'code': 'not_exactly_34_environments', 'inventory': len(inventory_rows), 'mapping': len(map_rows)})
    original = {item['id']: item for item in inventory_rows}
    if len(original) != len(inventory_rows) or Counter(item.get('id') for item in map_rows) != Counter(original.keys()):
        gaps.append({'code': 'mapping_environment_ids_not_exact_original_set'})
    if mapping.get('statement_inventory') != inventory_path.name or mapping.get('statement_inventory_sha256') != INVENTORY_SHA:
        gaps.append({'code': 'map_inventory_binding_mismatch'})
    if mapping.get('entry_module') != ENTRY:
        gaps.append({'code': 'final_entry_mismatch', 'expected': ENTRY})
    for field in ('known_exact_statement_gaps', 'pending_scope_review'):
        if mapping.get(field): gaps.append({'code': 'mapping_'+field, 'items': mapping[field]})
    manuscript_files = []
    for item in inventory.get('active_files', []):
        path = audit.root/'source/latest-429d53b'/item['path']
        raw = audit.read(path)
        accepted = raw is not None and digest(raw) == item['sha256'].upper()
        manuscript_files.append({'path': str(path.relative_to(audit.root)).replace('\\', '/'),
                                 'sha256': digest(raw) if raw is not None else None, 'accepted': accepted})
        if not accepted: gaps.append({'code': 'original_manuscript_file_changed', 'path': item['path']})
    declarations, statements = {}, []
    for item in map_rows:
        errors, expected = [], original.get(item.get('id'), {})
        for key in ('number', 'kind', 'labels'):
            if item.get(key) != expected.get(key): errors.append('original_'+key+'_mismatch')
        if item.get('manuscript_statement_sha256') != expected.get('statement_sha256'):
            errors.append('original_statement_hash_mismatch')
        if item.get('manuscript_statement_tex') != expected.get('statement_tex'):
            errors.append('original_statement_text_mismatch')
        if item.get('manuscript_source') != expected.get('source'):
            errors.append('original_statement_source_location_mismatch')
        if not item.get('lean_declarations'): errors.append('no_lean_declaration_mapping')
        for selected in item.get('lean_declarations', []):
            name, module = selected.get('name', ''), selected.get('module', '')
            key = (module, name)
            if key not in declarations:
                failures, current = [], None
                try:
                    record = audit.module(module)
                    declaration_text = audit.text(audit.root/'Lean'/module)
                    current = declaration_source(declaration_text, name)
                    if name not in {value['name'] for value in qualified_declarations(declaration_text)}:
                        failures.append('full_declaration_name_not_defined_in_mapped_module')
                    for field, value in current.items():
                        if selected.get(field) != value: failures.append(field+'_map_mismatch')
                    if selected.get('module_source_sha256') != record['source_sha256']:
                        failures.append('module_source_sha256_map_mismatch')
                    if current['declaration_kind'] == 'axiom': failures.append('mapped_article_declaration_is_axiom')
                except (ValueError, OSError) as error:
                    failures.append(str(error))
                declarations[key] = {'name': name, 'module': module, 'current': current,
                                     'map_failures': failures, 'mapped_environment_ids': []}
            else:
                current = declarations[key]['current']
                if current:
                    for field, value in current.items():
                        if selected.get(field) != value:
                            declarations[key]['map_failures'].append(field+'_map_mismatch_in_'+item['id'])
                if selected.get('module_source_sha256') != audit.modules[module]['source_sha256']:
                    declarations[key]['map_failures'].append('module_source_sha256_map_mismatch_in_'+item['id'])
            declarations[key]['mapped_environment_ids'].append(item['id'])
        statements.append({'id': item.get('id'), 'number': item.get('number'), 'kind': item.get('kind'),
                           'map_failures': errors,
                           'declarations': [{'module': value['module'], 'name': value['name']}
                                            for value in item.get('lean_declarations', [])]})
    audit.closure([DEFAULT_ROOT_ENTRY, ENTRY]+[module for module, _ in declarations])
    entry_closure = set()
    def visit_entry(module):
        if module in entry_closure: return
        entry_closure.add(module)
        for child in audit.modules[module]['dependencies']: visit_entry(child)
    visit_entry(ENTRY)
    entry = audit.module(ENTRY)
    default_root = check_default_root_entry(audit)
    if not default_root['accepted']:
        gaps.append({'code': 'default_root_entry_not_accepted', 'failures': default_root['failures']})
    if mapping.get('entry_source_sha256') != entry['source_sha256']:
        gaps.append({'code': 'entry_source_sha256_map_mismatch'})
    allowed, registers, registry_errors, native_authorized = registry(audit)
    gaps.extend(registry_errors)
    source_prints = Counter(re.findall(r'^\s*#print\s+axioms\s+([^\s]+)',
                                      strip_lean(audit.text(audit.root/'Lean'/ENTRY)), re.M))
    all_prints, axiom_union, classified_cache = entry['axiom_prints'], {}, {}
    def classify(name):
        if name not in classified_cache:
            classified_cache[name] = classify_axiom(name, allowed, native_authorized, audit.modules)
        return classified_cache[name]
    for selected in declarations.values():
        failures = selected['map_failures']
        if selected['module'] not in entry_closure: failures.append('mapped_module_not_imported_by_final_All')
        selected['current_dependency_closure'] = audit.modules[selected['module']]['current_dependency_closure']
        current = selected['current']
        if current and current['declaration_kind'] in ('theorem', 'lemma'):
            name = selected['name']
            records = [record for record in all_prints if record['declaration_as_printed'] == name]
            selected['final_All_source_print_count'] = source_prints[name]
            selected['final_All_actual_axiom_prints'] = records
            if not source_prints[name]: failures.append('final_All_source_missing_print_axioms')
            if len(records) != source_prints[name] or not records:
                failures.append('final_All_actual_axiom_print_missing_or_count_mismatch')
            if len({tuple(record['axioms_as_printed']) for record in records}) > 1:
                failures.append('inconsistent_repeated_axiom_prints')
            for record in records:
                record['classified_axioms'] = [{key: classify(value)[key] for key in ('name_as_printed', 'category', 'accepted')}
                                                for value in record['axioms_as_printed']]
                for value in record['axioms_as_printed']:
                    classified = classify(value)
                    axiom_union[classified['name_as_printed']] = classified
                    if not classified['accepted']: failures.append('forbidden_or_unregistered_axiom: '+classified['name_as_printed'])
        selected['accepted'] = bool(not failures and selected['current_dependency_closure'] and
                                    entry['current_dependency_closure'])
    explicit_axiom_failures = []
    for module in audit.modules.values():
        for axiom in module['explicit_source_axioms']:
            if axiom['name'] not in allowed:
                explicit_axiom_failures.append({'module': module['module'], 'name': axiom['name'],
                                                'source_line': axiom['source_line']})
    for item in statements:
        item['accepted'] = bool(not item['map_failures'] and all(
            declarations[(value['module'], value['name'])]['accepted'] for value in item['declarations']))
    observed_current_axioms = set()
    for module in audit.modules.values():
        for printed in module['axiom_prints']:
            printed['own_current_source_compiler_evidence'] = module['own_current_source_exit_zero']
            if module['own_current_source_exit_zero']:
                printed['classified_axioms'] = [{key: classify(value)[key] for key in ('name_as_printed', 'category', 'accepted')}
                                                for value in printed['axioms_as_printed']]
                observed_current_axioms.update(printed['axioms_as_printed'])
    if audit.cycles: gaps.append({'code': 'local_import_cycle', 'cycles': audit.cycles})
    if explicit_axiom_failures: gaps.append({'code': 'unregistered_explicit_source_axioms', 'declarations': explicit_axiom_failures})
    gaps.extend(audit.errors)
    changed = audit.changed_inputs()
    if changed: gaps.append({'code': 'inputs_changed_during_audit_rerun_required', 'paths': changed})
    failures = [item for item in audit.modules.values() if not item['current_dependency_closure']]
    baselines = {'Root': [], 'First': [], 'LastAE': []}
    for name in audit.ordered:
        module = audit.modules[name]
        if name not in entry_closure or module['own_failures'] != ['compiler_end_missing_or_ambiguous']:
            continue
        if module['dependency_source_freshness_failures']:
            continue
        if 'END_UTC=' in audit.text(audit.root/module['canonical_log']):
            continue  # An ambiguous or malformed END is not a missing-END baseline.
        owner = 'First' if name.startswith('LambdaCantor/First/') else (
            'LastAE' if name.startswith(('LambdaCantor/Last/', 'LambdaCantor/AE/')) else 'Root')
        baselines[owner].append({key: module[key] for key in
            ('module', 'source_sha256', 'log_source_sha256', 'canonical_log', 'log_start_utc',
             'log_exit', 'olean_exists', 'olean_bytes', 'olean_mtime_ns')})
    baseline_names = {item['module'] for rows in baselines.values() for item in rows}
    for module in audit.modules.values():
        reasons = module['own_failures']
        if module['module'] in baseline_names:
            state = 'legacy_success_missing_END_metadata_only'
        elif 'source_missing' in reasons:
            state = 'source_missing'
        elif 'compiler_source_sha_mismatch' in reasons:
            state = 'source_changed_since_logged_build'
        elif 'compiler_exit_nonzero' in reasons:
            state = 'actual_compile_failed'
        elif 'compiler_log_missing' in reasons:
            state = 'actual_compile_not_recorded'
        elif reasons:
            state = 'incomplete_or_invalid_own_evidence'
        elif module['dependency_source_freshness_failures']:
            state = 'transitive_dependency_source_newer_than_artifact'
        elif not module['current_dependency_closure']:
            state = 'own_build_passed_dependency_evidence_pending'
        else:
            state = 'current_build_and_dependency_sources_accepted'
        module['evidence_state'] = state
        module['blocked_dependencies'] = [child for child in module['dependencies']
                                          if not audit.modules[child]['current_dependency_closure']]
    accepted = bool(len(statements) == 34 and default_root['accepted'] and
                    entry['current_dependency_closure'] and not gaps and not failures and
                    all(item['accepted'] for item in statements))
    return {'schema_version': 1, 'accepted': accepted,
            'status': 'ACCEPTED_CURRENT_COMPILER_EVIDENCE' if accepted else 'NOT_ACCEPTED_REAL_GAPS_REMAIN',
            'started_utc': started, 'finished_utc': datetime.now(timezone.utc).isoformat(),
            'paper_commit': PAPER, 'fixed_environment_count': 34,
            'inventory_sha256': digest(inventory_raw) if inventory_raw else None,
            'declaration_map_sha256': digest(map_raw) if map_raw else None,
            'checker_sha256': digest(checker_raw),
            'policy': {'no_legacy_baseline_exceptions': True, 'current_source_sha_exit0_and_END_required_per_local_module': True,
                       'freshness_policy': 'newest transitive dependency SOURCE mtime <= importer olean mtime; unchanged-source dependency recompilation does not invalidate consumers',
                       'final_All_actual_axiom_print_required_for_every_mapped_theorem_lemma': True,
                       'default_root_must_import_actual_All_and_have_current_compiler_and_closure_evidence': True,
                       'default_root_need_not_duplicate_All_axiom_prints': True,
                       'sorryAx_and_unregistered_axioms_rejected': True, 'starts_compiler': False,
                       'modifies_Lean_map_or_inventory': False, 'uploads': False},
            'summary': {'mapped_environments': len(statements), 'mapped_declarations': len(declarations),
                        'required_final_axiom_prints': sum(item['current'] is not None and item['current']['declaration_kind'] in ('theorem', 'lemma')
                                                           for item in declarations.values()),
                        'actual_final_All_axiom_prints': len(all_prints), 'local_dependency_modules': len(audit.modules),
                        'own_current_source_EXIT0_modules': sum(item['own_current_source_exit_zero'] for item in audit.modules.values()),
                        'fully_current_closure_modules': len(audit.modules)-len(failures),
                        'missing_sources': [item['module'] for item in failures if item['source_sha256'] is None],
                        'unregistered_explicit_axioms': explicit_axiom_failures},
            'gaps': gaps, 'original_manuscript_files': manuscript_files, 'external_registers': registers,
            'default_root_entry': default_root,
            'registered_external_names': sorted(allowed),
            'legacy_baseline_rechecks': {'classification': 'Current source SHA, EXIT0 and olean match; only END is absent. Metadata recheck, not an identified mathematical proof gap. No acceptance exception is granted.',
                                        'ordered_by_local_import_topology': True, 'owners': baselines},
            'final_All_actual_axiom_union': [axiom_union[name] for name in sorted(axiom_union)],
            'observed_current_local_module_axiom_union': [classify(name) for name in sorted(observed_current_axioms)],
            'statements': statements, 'declarations': list(declarations.values()),
            'modules_in_topological_order': [audit.modules[name] for name in audit.ordered],
            'verification_boundary': 'Reads actual local compiler logs/artifacts; does not rerun Lean or prove the semantic prose-to-Lean correspondence. Imported Mathlib/Lean packages are the existing precompiled environment, listed per module; every project-local module has the same strict evidence rule.'}


def main():
    try:
        report = run()
    except Exception as error:
        report = {'schema_version': 1, 'accepted': False, 'status': 'AUDIT_FAILED_CLOSED',
                  'paper_commit': PAPER, 'error': type(error).__name__+': '+str(error),
                  'finished_utc': datetime.now(timezone.utc).isoformat()}
    output = ROOT/'MANUSCRIPT_ACCEPTANCE.json'
    output.write_text(json.dumps(report, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    for owner in ('Root', 'First', 'LastAE'):
        queue = ROOT/f'manuscript-legacy-baselines-{owner}.txt'
        rows = report.get('legacy_baseline_rechecks', {}).get('owners', {}).get(owner, [])
        queue.write_text(''.join(row['module']+'\n' for row in rows), encoding='utf-8')
    print(json.dumps({'accepted': report['accepted'], 'status': report['status'],
                      'summary': report.get('summary'), 'error': report.get('error'),
                      'report': str(output)}, ensure_ascii=False), flush=True)
    return 0 if report['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
