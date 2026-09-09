# The price of repeated evidence: sharp monitoring costs and hidden higher-order overlap

Lean verification source for the manuscript by **Gil Alterovitz**.

All **335 theorem and lemma declarations in 63 modules** passed Lean 4.19.0.
The claim inventory covers all principal mathematical statements under their
stated assumptions. The declaration count includes auxiliary results and is
neither a count of discoveries nor a percentage of manuscript coverage.

## Reproduce

Install Lean's toolchain manager (elan), Git, and Python 3, then run from this
directory:

```sh
lake exe cache get
python3 verify.py
```

The manifests pin Lean **4.19.0** and Mathlib commit
**c44e0c8ee63ca166450922a373c7409c5d26b00b**, including its transitive dependencies.
If official cache objects are unavailable, build the pinned dependencies from
source with Lake before running the verifier. Compiled dependency objects are
not included in this source release. The first dependency installation can be
large and time-consuming.

The verifier deletes this project's `.lake/build` directory, compiles each
project module from source in dependency order, audits the transitive axioms of
all 335 declarations, and requires the false-statement control to fail for its
expected reason. `python3 verify_std.py` separately checks the 41 declarations
in three combinatorial modules using Lean alone. The negative control is
intentionally false; its rejection is a successful control outcome.

## Coverage and proof correspondence

`paper_coverage.json` maps manuscript claims to named Lean declarations.
Accepted results include the universal monitoring model, Ville bounds, general
Finner inequality, finite-cost criterion, attained Finner optimization,
weighted gamma attainment, regular designs, the overlap hierarchy, source
reconstruction, capped penalties, pooled quantile optimality and attainment,
the strict optimized gap, and the equal-leaf Erlang integral formula. Reporting
and false-discovery-control results retain their explicit assumptions.

The manuscript's revised Corollary 5 follows `PooledStrictGap.lean`: strict
global Holder inequality is combined with the exponential-versus-affine-gamma
obstruction. Second and third derivatives of the log moment generating
functions exclude equality for two or more leaves. This replaces the original
manuscript's conditional Holder and hazard argument.

## Verification evidence and limits

`verification_logs/verification_result.json` records the accepted build,
axiom audit, expected negative-control rejection, and Lean source SHA-256
hashes. Build and audit transcripts accompany that result. `ProofAudit.lean`
prints dependencies on axioms; the audit permits only `propext`,
`Classical.choice`, and `Quot.sound`. There are no unfinished proofs, native
decision proofs, or added mathematical axioms. Lean's kernel and the pinned
compiled dependencies remain part of the trust boundary.

The published Lean files were checked byte for byte against the hashes of the
successful verification run. `SOURCE_MANIFEST.sha256.json` also inventories
this source release; it is an integrity check, not another proof check.

`principal_mathematical_claims_verified` is true. The result deliberately keeps
`paper_verification_complete` false: Lean does not certify historical novelty,
biological assumptions, empirical outputs, or publication suitability.
Empirical data and analysis scripts are not included in this proof folder.
