# Certifying biomedical model comparisons by fusing overlapping outcome summaries

Lean verification source

The project accompanies *Certifying biomedical model comparisons by fusing overlapping outcome summaries*. This public source release records the successful verification completed on September 9, 2026.

**All three main theorems and the supplementary disjoint-group minimax theorem have accepted Lean proofs.** The final clean run accepted 305 theorem declarations across 29 modules, with no placeholders or custom axioms. The count includes auxiliary lemmas and examples, not 305 new scholarly results. This is not a verification of all manuscript prose, empirical software, datasets, or scholarly novelty.

## Main declarations

| Paper result | Lean declarations | Scope |
|:--|:--|:--|
| Theorem 1 | `FusionPaper.theorem1`, `FusionPartition.two_partition_sharp` | Binary endpoints bound every feasible real relaxed completion, including count intervals and reviews |
| Theorem 2 | `FusionPaper.theorem2_all_finite`, `FusionHierarchy.two_laminar_sharp` | Arbitrary finite laminar input families; explicit flow construction for nonempty cohorts, trivial empty-cohort endpoints included separately |
| Theorem 3 | `FusionTree.two_partition_separation`, `FusionTree.exact_numeric_budgets`, `FusionTree.normalized_exactness` | Every depth, two exact-count partitions, rank permutations, fixed budget 2^k, adaptive budget k+1 on actual feasible inputs |
| Equation S8 | `FusionDisjoint.review_set_minimax`, `FusionDisjoint.fixed_adaptive_minimax` | Nonempty permitted families, arbitrary additive vector targets and every norm, finite deterministic policies including repeated queries |
| Pairwise area identity | `FusionAUROC.pairwise_rank_sum`, `FusionAUROC.paired_area_contrast` | Derivation from wins and half-tie credit, including tied scores |
| Equation 6 | `Fusion.coarsening_bound`, `Fusion.rank_prefix_eight_bound` | General cumulative-count bound and the stated 8(N-1) rank contribution |
| Equation S7 | `Fusion.difference_set_identity`, `FusionDisjoint.diameter_eq_potential` | General additive difference set and attained maximum over all group completions |
| Section S4.3 reduction | `FusionSlack.transcript_target_equivalence`, `FusionSlack.grouped_slack_encoding` | Binary slack subsets and unchanged feasible targets under original-record observation restrictions |

## Integral endpoint proof

`FusionNetwork.fractional_connected` derives an alternate fractional path by a cut argument. `fractional_circulation` builds a nonzero circulation supported on fractional edges. `rounding_step` chooses a cost-nonincreasing direction and moves until a coordinate reaches an integer boundary. All integer bounds and balances survive, and the number of fractional coordinates strictly decreases. `real_flow_rounding` concludes by strong induction.

`integral_flow_extrema` combines rounding with attained extrema over the finite integer box. Thus both real relaxed optima are attained by integral flows. Real feasibility, the cost inequality, and integrality are proved rather than assumed. The proof includes loops, parallel arcs, integer lower and upper bounds, and arbitrary real costs.

`PartitionNetwork` proves the real count/flow lifting and projection and objective correspondence. `LaminarNetwork` and `LaminarFusion` prove the analogous completed-tree graph representation for two arbitrary laminar families. The endpoint proof uses constructive rounding as an alternative to the paper's textual total-unimodularity argument.

## Minimax semantics

`DisjointGame` constructs a fixed compatible labeling realizing the majority answers. `DisjointSemantics` preserves the full positive labeling through execution. `DisjointRealization.residual_realization` proves that every compatible residual completion at a reached state is realized by a compatible initial labeling reaching that same state. These results anchor terminal diameters to feasible input labelings.

The maximum is taken over finite completion sets. Its real-valued `measure` argument is arbitrary, hence can be instantiated with any norm on the additive target group. `DisjointReviewSets` starts with no reviewed positives, converts original review sets to remaining sets, proves the fixed list queries exactly the chosen set, and proves every prefix is allowed when the family is downward closed. The lower bound covers all legal terminal-set policies, hence also policies constrained at every prefix.

**Statement clarification:** Supplementary S4.2 explicitly assumes the permitted review-set family is nonempty. Downward closure alone allows the empty family, for which a minimizing set does not exist. `FusionDisjoint.empty_review_family` proves this counterexample. The finalized supplement includes this nonempty-family assumption. The mathematical manuscript and empirical datasets are not part of this source release.

## Reproduce

Install Lean 4.19.0. The Lake files pin Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` and its dependencies. From the project directory:

```sh
lake exe cache get
python3 verify.py
```

Dependency downloads require network access. The verifier removes all local compiled proof outputs, compiles all delivered modules in dependency order with `lake env lean`, compiles the aggregate import, and separately runs `Audit.lean`. It does not rely on previously compiled local proofs or claim a separate `lake build` run. The successful command outputs, exit codes, theorem names, axiom lists, and exact source hashes are in `verification_logs`.

Every `theorem` and `lemma` is audited. Proof sources are screened for `sorry`, `admit`, custom `axiom`, `unsafe`, and `native_decide` tokens. The audit requires every dependency to belong to `{propext, Classical.choice, Quot.sound}`. Ordinary unused-variable and tactic-style linter warnings are not proof obligations.

The optional `container_compat/proc_self_compat.c` addresses this container's process-directory mismatch. Ordinary installations should not need it. If affected:

```sh
cc -shared -fPIC -O2 -o proc_self_compat.so container_compat/proc_self_compat.c -ldl
```

Run the verifier with `LD_PRELOAD` set to that shared library's absolute path. It maps only the current process executable lookup from `/proc/<getpid>/exe` to `/proc/self/exe`; it changes no Lean kernel or Mathlib logic. Public dependency source code was not changed.

## Module inventory

| Module | Theorem declarations |
|:--|--:|
| AUROC | 5 |
| Basic | 14 |
| Disjoint | 8 |
| DisjointDiameter | 10 |
| DisjointGame | 12 |
| DisjointMinimax | 15 |
| DisjointRealization | 1 |
| DisjointReviewSets | 10 |
| DisjointSemantics | 4 |
| Endpoints | 4 |
| Finite | 8 |
| Flow | 6 |
| Laminar | 11 |
| LaminarComplete | 9 |
| LaminarFusion | 14 |
| LaminarNetwork | 13 |
| MainTheorems | 5 |
| NetworkOpt | 4 |
| NetworkRounding | 15 |
| NetworkStep | 8 |
| PartitionNetwork | 12 |
| RankVariation | 4 |
| Review | 12 |
| Separation | 27 |
| Slack | 4 |
| Tree | 22 |
| TreeCounts | 21 |
| TreeRank | 13 |
| Variation | 14 |

## Scope boundaries

- The constructive proof establishes integral endpoints. Matrix total unimodularity itself and a minimum-cost-flow implementation are not formally verified.
- The laminar specification indexes all finite subsets and forces inactive arcs to zero. No compact graph-size or polynomial runtime theorem is claimed for that expanded specification.
- Review results concern diameter and finite deterministic policies, not randomized policies or minimum enclosing radius.
- The bounded-total slack reduction is proved as transcriptwise target-set equivalence. A separately named bounded-total policy minimax assembly is not included.
- Biomedical data processing, floating-point optimization, empirical results, novelty, clinical benefits, and journal acceptance are outside the formal verification.

The current audit is `verification_logs/summary.json`. Its source hashes match every published proof, verification script, and pinned dependency file. The package manifest hashes every published file except itself. The manuscript reports the formalization briefly and links here; the empirical reproducibility package is supplied separately with the submission. No independent human formalization review is claimed.

## Author

Gil Alterovitz, Harvard Medical School. Correspondence: ga@alum.mit.edu.
