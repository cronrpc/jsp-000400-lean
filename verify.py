"""Rebuild local modules and check their audited theorem dependencies."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time
from datetime import datetime, timezone

root = Path(__file__).resolve().parent
out = root / 'verification'
out.mkdir(exist_ok=True)
results = []
started_utc = datetime.now(timezone.utc).isoformat()
library_roots = re.findall(r'`([A-Za-z0-9_]+)', (root/'lakefile.lean').read_text())
expected_modules = {p.stem for p in root.glob('*.lean')} - {'Audit', 'lakefile'}
assert set(library_roots) == expected_modules, (set(library_roots), expected_modules)

FINAL_THEOREMS = [
    'JSP400.positive_statement', 'JSP400.dual_statement',
    'JSP400.erdos_496', 'JSP400.erdos_496_large_denominator',
]
expected_audits = re.findall(r'^#print axioms (\S+)', (root/'Audit.lean').read_text(), re.M)
missing_final_audits = set(FINAL_THEOREMS) - set(expected_audits)
if missing_final_audits:
    raise RuntimeError(f'Final theorems missing direct axiom audits: {sorted(missing_final_audits)}')
final_theorem_axioms = {}

def code_without_comments(source):
    """Remove nested Lean comments and strings before checking proof commands."""
    output = []
    i, depth, string = 0, 0, False
    while i < len(source):
        pair = source[i:i+2]
        if depth:
            if pair == '/-': depth += 1; i += 2
            elif pair == '-/': depth -= 1; i += 2
            else: i += 1
        elif string:
            if source[i] == '\\': i += 2
            elif source[i] == '"': string = False; i += 1
            else: i += 1
        elif pair == '/-': depth = 1; i += 2
        elif pair == '--':
            j = source.find('\n', i)
            i = len(source) if j == -1 else j
        elif source[i] == '"': string = True; i += 1
        else: output.append(source[i]); i += 1
    return ''.join(output)

scanned = []
for path in sorted(root.rglob('*.lean')):
    if any(part in {'.lake', '.git'} for part in path.relative_to(root).parts):
        continue
    code = code_without_comments(path.read_text(encoding='utf-8-sig'))
    assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b', code), str(path)
    scanned.append(str(path.relative_to(root)))

git_commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
actual_mathlib = subprocess.check_output(
    ['git', 'rev-parse', 'HEAD'], cwd=root/'.lake/packages/mathlib', text=True).strip()
assert actual_mathlib == '5ed2965256430c3649e86755f9576b54eca72435', actual_mathlib
for name, cmd in [('build', ['lake', 'build']),
                  ('axioms', ['lake', 'env', 'lean', '-j1', 'Audit.lean'])]:
    start = time.monotonic()
    proc = subprocess.run(cmd, cwd=root, text=True, capture_output=True)
    output = proc.stdout + proc.stderr
    (out / (name + '.log')).write_text(output)
    result = dict(check=name, command=cmd, exit_code=proc.returncode,
                  elapsed_seconds=time.monotonic()-start)
    if proc.returncode != 0:
        print(output)
        sys.exit(proc.returncode)
    if name == 'axioms':
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
        expected = expected_audits
        assert set(expected) == {n for n, _ in audits}, (expected, audits)
        allowed = {'propext', 'Classical.choice', 'Quot.sound'}
        for theorem, dependencies in audits:
            actual = {x.strip() for x in dependencies.split(',') if x.strip()}
            assert actual <= allowed, (theorem, actual)
        dependencies_by_theorem = {
            theorem: sorted(x.strip() for x in dependencies.split(',') if x.strip())
            for theorem, dependencies in audits
        }
        missing_final_results = set(FINAL_THEOREMS) - set(dependencies_by_theorem)
        if missing_final_results:
            raise RuntimeError(f'Final theorems missing axiom results: {sorted(missing_final_results)}')
        final_theorem_axioms = {name: dependencies_by_theorem[name] for name in FINAL_THEOREMS}
        result['audited_theorems'] = len(audits)
        result['directly_audited_final_theorems'] = FINAL_THEOREMS
    results.append(result)
checked_sources = sorted({root/(name+'.lean') for name in library_roots}
                         | {root/'Audit.lean', root/'lakefile.lean', root/'verify.py',
                            root/'lean-toolchain', root/'lake-manifest.json', root/'README.md'})
manifest = {
    'started_utc': started_utc,
    'completed_utc': datetime.now(timezone.utc).isoformat(),
    'git_commit_at_verification': git_commit,
    'checks': results,
    'source_scan': {'forbidden_commands_found': [], 'scanned_files': scanned},
    'lean_toolchain': (root/'lean-toolchain').read_text().strip(),
    'source_sha256': {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in checked_sources},
    'library_roots': library_roots,
    'mathlib_commit': '5ed2965256430c3649e86755f9576b54eca72435',
    'complete_problem_proved': True,
    'proved_target': 'For every positive irrational real alpha and every epsilon > 0, '
                     'both inequalities of Erdos I.34 have positive integer witnesses.',
    'final_theorems': FINAL_THEOREMS,
    'final_theorem_axioms': final_theorem_axioms,
}
(out/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps(manifest, indent=2))
