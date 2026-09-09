# More neighbors, less progress: Sharp limits of hub averaging

Lean verification source

This project formalizes the five numbered mathematical results in **More neighbors,
less progress: Sharp limits of hub averaging**. The final clean run accepted **153 supporting theorems in 17 modules**.
The theorem count is a count of supporting statements, not 153 separate paper results.

## Reproduce

Install Lean using the [official instructions](https://lean-lang.org/install/).
The `lean-toolchain` file selects Lean 4.19.0. The Lake manifest pins Mathlib at
`c44e0c8ee63ca166450922a373c7409c5d26b00b` and pins its dependencies.

From this directory:

```sh
python3 verify.py --fetch-cache
```

If the pinned dependency objects are already installed, use `python3 verify.py`.
The optional `--jobs 1` setting compiles one proof module at a time; the default is two.
Fetching the dependency cache requires network access. A standard `lake build` is
also available; the verification runner uses direct Lean compilation to avoid
unnecessary dependency rebuilds in hosted environments.

The runner deletes all 17 local proof objects, recompiles them in dependency order
with `warningAsError=true`, and queries `#print axioms` for every exported theorem.
It rejects unfinished proofs, added axioms, native evaluation in proof sources, and
any axiom dependency outside `propext`, `Classical.choice`, and `Quot.sound`.
It checks the Lean version, Mathlib commit, and that the pinned Mathlib mathematical
sources and configuration are unmodified. It records source hashes, logs, and a
machine-readable result. Failures produce a failure record and a nonzero exit status.

## Manuscript entry points

| Result | Principal accepted theorems |
| --- | --- |
| Lemma 1 | `hubMeanLoss_local_identity`, `coefficient_bounds` |
| Proposition 2 | `uniform_graph_operator`, `exists_uniform_spectral_endpoints` |
| Theorem 3 | `bipartite_policy_lower_bound`, `exact_bipartite_minimax` |
| Corollary 4 | `edgeWorst_bound`, `edge_budget_exponential`, `equal_budget_separation_graph`, `vanishing_separation` |
| Proposition 5 | `arbitrary_random_cut_bound`, `cutMaximum_le` |

All declarations are in namespace `HubAveraging`. The full theorem-to-axiom list is
in `verification/verification_results.json` and `verification/axioms.log`.

## What is now connected

The physical pair update and distinct-neighbor graph sweep are defined explicitly.
The local expectation is proved first by sampling without replacement and then
by reindexing the literal uniform distribution on permutations. The graph moment
identities and actual uniform-policy operator are derived, not assumed.

Mathlib's spectral theorem constructs the eigenbasis. Connectivity removes the
constant mode, regularity supplies the upper spectral bound, and the extremal
nonzero eigenvalues are shown to exist. The spectral-gap condition is expressed
as a lower bound on every nonzero Laplacian eigenvalue. This is the usual
spectral-gap condition for the connected graphs in the paper.

Sweep policies are arbitrary input-dependent probability laws on the finite set
of actual hub/order actions. Their worst residual and optimum use Lean's real
supremum and infimum; the needed bounds and witnesses are proved. Uniform action
selection is shown to mean uniform hubs and uniform orders on a regular graph.

Independent edge choices are represented by repeated uniform finite expectation.
The graph Poincare inequality, conditional contraction, equal-budget bound, valid
spectral-gap range, and limit over families of finite graphs are all proved.
Choosing either orientation of an undirected edge gives the same physical update.

The cut theorem permits an arbitrary probability space and arbitrary real-valued
outputs preserving the selected closed-neighborhood sum. Its nonnegative extended
expectation includes the infinite-expected-energy case. The maximum cut constant
and its bound in terms of the number of same-part neighbors are proved.

## Scope and trust boundary

The five numbered results have complete formal proofs under their stated domain
conditions. The local identity requires positive degree; ratios require positive
initial disagreement. The manuscript model explicitly states `N >= 2`.

This does not certify every sentence or ancillary example in the manuscript.
The Python experiments, figures, 103-graph numerical study, specific example-graph
spectra, novelty and priority claims, journal suitability, and interpretation of
references are outside the Lean certificate. The degree-500 rational comparison
is certified as arithmetic; the entire concrete example is not separately
instantiated as a Lean graph. No minimum-randomness theorem is claimed.

The accepted terms use the official Lean 4.19.0 release and pinned Mathlib.
No independent external proof checker was run. The standard axioms listed above
remain part of the trusted logical foundation.

The hosted environment blocks locating the current executable through
`/proc/<own-pid>/exe` but exposes `/proc/self/exe`. The disclosed compatibility
source changes only that lookup. It does not change the kernel or proof terms.
Ordinary Linux installations do not need it. In an environment with the same issue:

```sh
cc -shared -fPIC environment/self_path_compat.c -ldl -o environment/self_path_compat.so
export LD_PRELOAD="$PWD/environment/self_path_compat.so"
python3 verify.py --fetch-cache
```

This repository folder contains the verification source, pinned dependency files,
and the successful audit logs. The manuscript and Word verification report are
distributed separately. The manuscript model explicitly excludes the trivial
one-vertex case. The source hashes in `verification/verification_results.json`
match the exact files checked by the recorded clean run.

## Technical sources

- [Lean proof validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
- [Lean 4.19.0 release](https://github.com/leanprover/lean4/releases/tag/v4.19.0)
- [Pinned Mathlib source](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b)

ChatGPT through Codex, developed by OpenAI, assisted the formalization and analysis.
