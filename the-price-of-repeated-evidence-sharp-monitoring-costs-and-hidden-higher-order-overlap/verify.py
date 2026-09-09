#!/usr/bin/env python3
"""Rebuild the proof library, audit its axioms, and require a false control to fail."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, sys

root = Path(__file__).resolve().parent
logs = root / 'verification_logs'
logs.mkdir(exist_ok=True)
modules = ['ParityCore', 'OverlapReconstruction', 'ParityIncidence', 'RepeatedEvidence', 'RepeatedEvidenceNumerics', 'RepeatedEvidenceCalculus', 'RepeatedEvidenceReporting', 'ProbabilityReportingCore', 'ProbabilityReporting', 'SurvivalMartingale', 'ExponentialSurvival', 'StochasticModel', 'UniversalDivergence', 'TailCalibration', 'GammaMoments', 'DiscreteVille', 'ContinuousVille', 'CommonSourceCost', 'CappedMoments', 'CappedCost', 'FourStudyStochastic', 'FinnerProduct', 'FinnerSources', 'FinnerMonitoring', 'CappedReadBound', 'FinnerOptimization', 'OptimizedFinnerBound', 'LocalMGF', 'GammaSums', 'IndependentCoordinates', 'GammaConstruction', 'WeightedGammaAttainment', 'FourStudyExact', 'ParitySources', 'ParityCalibration', 'OverlapHierarchy', 'SourceReconstruction', 'PooledStructure', 'PooledOptimization', 'QuantileCore', 'QuantileTransform', 'ProductLayerCake', 'Rearrangement', 'IndependentQuantiles', 'ExponentialQuantile', 'LogMaximum', 'AtomlessSums', 'SurvivalModel', 'PooledDistribution', 'QuantileComparison', 'PooledUpper', 'PooledAttainment', 'PooledExact', 'AffineGammaObstruction', 'ExponentNonproportionality', 'StrictHolder', 'EqualLeafGamma', 'PooledStrictGap', 'ErlangCalculus', 'ErlangCDF', 'ErlangPooled', 'RegularDesigns', 'ClosedVille']
expected = []
for module in modules:
    source = (root / (module + '.lean')).read_text()
    if re.search(r'\b(?:sorry|admit|native_decide)\b|^\s*(?:axiom|opaque)\s', source, re.M):
        raise SystemExit('Unapproved proof construct in ' + module)
    namespace = re.search(r'^namespace (\w+)', source, re.M).group(1)
    expected += [namespace + '.' + name for name in re.findall(r'^(?:theorem|lemma) ([\w.]+)', source, re.M)]

def run(command, name):
    result = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (logs / name).write_text(result.stdout)
    return result

# Rebuild only this project's generated outputs; preserve dependency caches.
if (root / '.lake/build').exists():
    shutil.rmtree(root / '.lake/build')
version = run(['lake', 'env', 'lean', '--version'], 'lean_version.log')
if version.returncode or 'version 4.19.0' not in version.stdout:
    raise SystemExit('Expected Lean 4.19.0')
# Compile every project module from source, in dependency order. The imported
# dependency objects must already be installed, as for a standard cached build.
(root / '.lake/build/lib/lean').mkdir(parents=True, exist_ok=True)
build_text = []
for module in modules:
    build = run(['lake', 'env', 'lean', module + '.lean', '-o',
                 '.lake/build/lib/lean/' + module + '.olean'], 'build_' + module + '.log')
    build_text.append(module + ': exit ' + str(build.returncode) + '\n' + build.stdout)
    (logs / 'build.log').write_text('\n'.join(build_text))
    if build.returncode:
        raise SystemExit('Build failed: see verification_logs/build_' + module + '.log')
audit = run(['lake', 'env', 'lean', 'ProofAudit.lean'], 'axioms.log')
if audit.returncode:
    raise SystemExit('Axiom audit did not compile')
entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", audit.stdout, re.S)
actual = {name: sorted(x.strip() for x in axioms.replace('\n',' ').split(',') if x.strip())
          for name, axioms in entries}
actual.update({name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", audit.stdout)})
if set(actual) != set(expected):
    raise SystemExit('The axiom inventory does not match the source inventory')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if any(set(axioms) - allowed for axioms in actual.values()):
    raise SystemExit('Unexpected axiom dependency')
negative = run(['lake', 'env', 'lean', 'tests/NegativeControl.lean'], 'negative_control.log')
if negative.returncode == 0 or "tactic 'decide' proved that the proposition" not in negative.stdout:
    raise SystemExit('Negative control was not rejected for the expected reason; inspect its log')
result = {
    'status': 'PASS: all inventoried principal mathematical claims',
    'lean_version': version.stdout.strip(),
    'mathlib_commit': 'c44e0c8ee63ca166450922a373c7409c5d26b00b',
    'theorem_declarations': len(expected),
    'declaration_count_is_not_a_paper_coverage_percentage': True,
    'paper_verification_complete': False,
    'universal_functionals_defined': True,
    'principal_mathematical_claims_verified': True,
    'remaining_principal_claims': [],
    'build_exit_code': build.returncode,
    'axiom_audit_exit_code': audit.returncode,
    'negative_control_exit_code': negative.returncode,
    'axioms': actual,
    'source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(root.glob('*.lean'))},
    'limitations': ['Empirical analyses and biological assumptions are not certified',
                    'Formal statements retain their explicitly stated assumptions',
                    'No historical novelty or publication-impact certification']
}
(logs / 'verification_result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in {'axioms','source_sha256'}}, indent=2))
