# Limits and design of evidence fusion under adaptive replacement

Completed Lean formalizations for the paper by Gil Alterovitz.

All fifteen numbered mathematical results S1 through S15 have completed formal
formulations. Lean accepted 252 theorem declarations, including supporting
lemmas, across 44 modules in a fresh project build. The full axiom audit passed
again before publication. No numbered result was rejected. An intentionally
false report-count assertion was rejected as a negative control.

## Reproduce

Install Elan, Git and Python 3, then run:

```sh
git clone --branch add-adaptive-replacement-evidence-fusion-proofs https://github.com/bcl-lab/proofs.git
cd proofs/limits-and-design-of-evidence-fusion-under-adaptive-replacement
lake exe cache get
python3 verify.py
```

The included toolchain pins Lean 4.19.0. Mathlib is pinned to commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. The verification script removes only
this project's generated build directory, rebuilds positive modules in
dependency order, audits every theorem and requires the false control to fail.
The expected result is `status: passed`, 252 accepted declarations, zero
admitted proofs and zero custom axioms. Compilation is resource intensive.

## Results and coverage

See [coverage.json](coverage.json) for the precise mapping and formulation notes,
and [theorem_inventory.json](theorem_inventory.json) for every audited declaration.
The source modules include the complete-class converse, exact admissibility,
design duality, exchangeable ranks, sequential validity, explicit universal
growth, the matching upper rate, and the pointwise capacity and report-count
bounds. The full S13 capacity theorem covers zero coordinates and an attaining
admissible rule for each fixed clean vector.

The manuscript update reports this verification and makes explicit that S9 uses
the independent and identically distributed alternative and logarithmic
integrability assumptions of S8. No theorem conclusion was weakened or removed.
The formal source distinguishes fixed-vector capacity attainment from selecting
weights on a tested observation. It distinguishes marginal rank calibration
from conditional sequential validity.

## Verification evidence and trust

- [verification_results.json](verification_results.json) records results,
  source hashes, foundational axioms and reviewed linter warnings.
- [build.log](build.log) records the fresh project compilation.
- [axiom_audit.log](axiom_audit.log) records every declaration and its axioms.
- [negative_control.log](negative_control.log) records the required failure of
  [FalseReportCount.lean](negative_controls/FalseReportCount.lean).
- [lean_version.log](lean_version.log) records the toolchain.
- [source_manifest.json](source_manifest.json) identifies the published bytes.

Only propositional extensionality (`propext`), classical choice
(`Classical.choice`) and quotient soundness (`Quot.sound`) are allowed. No
admissions, custom axioms or native-evaluation axioms occur. The dependency
cache was used; no independent second kernel checker was run. The small
process-path compatibility adapter used on the verification host is included
for inspection. It changes executable-path discovery, not proofs or the kernel.
Ordinary installations do not need it.

Lean checks the formal statements under their explicit hypotheses. Their
correspondence with manuscript prose was inspected, not automatically proved.
The empirical studies, dataset assumptions, every unnumbered numerical
illustration, execution-cost claims, novelty and clinical effectiveness are
outside this formalization. These files contain proof source, not the biomedical
data or empirical analysis pipeline. `input_manifest.json` records the hashes of
the manuscript and supplement originally reviewed; their document bytes are not
part of this public proof-source folder.

See the official [Lean proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
for the meaning of compilation and axiom checks, and the
[pinned Mathlib source](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b).
