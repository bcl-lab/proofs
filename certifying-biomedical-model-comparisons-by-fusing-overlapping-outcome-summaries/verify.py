"""Compile all local proofs with the pinned Lean, then audit every theorem.
Run: python3 verify.py (after dependency caches are available).
The local proof outputs are deleted first; Mathlib caches are retained.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess

ROOT = Path(__file__).resolve().parent
LOG = ROOT / 'verification_logs'
LOG.mkdir(exist_ok=True)
SUMMARY = LOG / 'summary.json'
summary = {'status': 'running', 'whole_paper_formally_verified': False}
SUMMARY.write_text(json.dumps(summary, indent=2) + '\n')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
modules = {p.stem: p for p in sorted((ROOT / 'Fusion').glob('*.lean'))}
order, visiting, names, by_module = [], set(), [], {}

def fail(message):
    summary.update(status='failed', reason=message)
    SUMMARY.write_text(json.dumps(summary, indent=2) + '\n')
    raise SystemExit(message)

def visit(module):
    if module in order:
        return
    if module in visiting:
        fail('Local import cycle: ' + module)
    visiting.add(module)
    path = modules[module]
    source = path.read_text()
    if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b', source):
        fail('Forbidden proof escape token in ' + path.name)
    namespaces = re.findall(r'^namespace\s+(\w+)\s*$', source, re.M)
    if len(namespaces) != 1:
        fail('Expected one explicit namespace in ' + path.name)
    local_names = [namespaces[0] + '.' + x for x in
                   re.findall(r'^(?:theorem|lemma)\s+([A-Za-z0-9_]+)', source, re.M)]
    if not local_names:
        fail('No theorem declarations found in ' + path.name)
    by_module[module] = local_names
    for dep in re.findall(r'^import\s+Fusion\.(\w+)', source, re.M):
        if dep not in modules:
            fail('Missing local dependency ' + dep)
        visit(dep)
    visiting.remove(module)
    order.append(module)
    names.extend(local_names)

for module in modules:
    visit(module)
if len(names) != len(set(names)):
    fail('Duplicate theorem names')
root_imports = set(re.findall(r'^import\s+Fusion\.(\w+)', (ROOT/'Fusion.lean').read_text(), re.M))
if root_imports != set(modules):
    fail('Fusion.lean must import exactly all delivered proof modules')
audit = 'import Fusion\n\n' + '\n'.join('#check ' + n + '\n#print axioms ' + n for n in names) + '\n'
(ROOT/'Audit.lean').write_text(audit)
output_dir = ROOT/'.lake/build/lib/lean/Fusion'
output_dir.mkdir(parents=True, exist_ok=True)
for module in modules:
    for ext in ['olean', 'ilean']:
        (output_dir/(module+'.'+ext)).unlink(missing_ok=True)
(ROOT/'.lake/build/lib/lean/Fusion.olean').unlink(missing_ok=True)

commands = [('lean_version', ['lake','env','lean','--version'])]
commands += [('compile_'+m, ['lake','env','lean','-o',
              '.lake/build/lib/lean/Fusion/'+m+'.olean','Fusion/'+m+'.lean']) for m in order]
commands += [('compile_Fusion',['lake','env','lean','-o','.lake/build/lib/lean/Fusion.olean','Fusion.lean']),
             ('axioms',['lake','env','lean','Audit.lean'])]
exits = {}
with (LOG/'build.log').open('w') as build:
    for label, command in commands:
        print(label, flush=True)
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        exits[label] = result.returncode
        (LOG/(label+'.log')).write_text(result.stdout)
        build.write('$ ' + ' '.join(command) + '\n' + result.stdout + '\nexit=' + str(result.returncode) + '\n\n')
        build.flush()
        if result.returncode != 0 or 'error:' in result.stdout:
            print(result.stdout)
            fail('Verification failed during ' + label)
text = (LOG/'axioms.log').read_text()
axioms = {name: [x.strip() for x in deps.split(',') if x.strip()]
          for name, deps in re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", text)}
axioms.update({name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", text)})
missing = sorted(set(names) - set(axioms))
unexpected = {name: deps for name, deps in axioms.items() if not set(deps) <= allowed}
if missing or unexpected or set(axioms) != set(names):
    fail(json.dumps({'missing': missing, 'unexpected_axioms': unexpected, 'extra': sorted(set(axioms)-set(names))}))
source_files = [modules[m] for m in order] + [ROOT/x for x in
               ['Fusion.lean','Audit.lean','verify.py','lean-toolchain','lakefile.toml','lake-manifest.json']]
summary = {
    'status': 'passed',
    'execution_clock_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'verification_method': 'All local proof outputs removed; lake env lean compiled every module and aggregate import; separate axiom audit',
    'lean_version': (LOG/'lean_version.log').read_text().strip(),
    'mathlib_revision': 'c44e0c8ee63ca166450922a373c7409c5d26b00b',
    'declarations': len(names), 'modules': len(modules), 'compile_order': order,
    'exit_codes': exits, 'declarations_by_module': by_module, 'axioms_by_declaration': axioms,
    'source_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files},
    'main_theorems_fully_formalized': [1, 2, 3], 'whole_paper_formally_verified': False,
    'closed_prior_obligations': [
        'Cost-nonincreasing rounding of arbitrary bounded real flows with integer bounds and balances',
        'Integral attainment of both endpoints over the full real-flow relaxation',
        'Explicit directed network encoding of arbitrary two-laminar-family constraints',
        'Disjoint-group diameter and fixed/adaptive minimax over nonempty allowed review families',
        'Fixed input witnesses for majority transcripts and realization of residual completions',
        'General tied-score AUROC identity derived from pairwise credit'
    ],
    'statement_clarifications': [
        'Supplementary S4.2 requires a nonempty permitted review-set family; downward closure alone is insufficient'
    ],
    'scope_limits': [
        'No verification of biomedical data processing, floating-point solver implementation, empirical results, or novelty',
        'Constructive integral endpoint proof replaces the textual total-unimodularity argument; matrix total unimodularity itself is not formalized',
        'No polynomial runtime or compact graph-size bound for the laminar encoding indexed by all finite subsets',
        'Finite deterministic query policies and diameter are formalized; randomized policies and enclosing radius are outside the statements',
        'Slack encoding is proved as transcriptwise target-set equivalence; no separately named bounded-total policy minimax assembly'
    ],
    'open_prior_proof_obligations': []
}
SUMMARY.write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps({k: summary[k] for k in ['status','declarations','modules','main_theorems_fully_formalized','whole_paper_formally_verified']}, indent=2))
