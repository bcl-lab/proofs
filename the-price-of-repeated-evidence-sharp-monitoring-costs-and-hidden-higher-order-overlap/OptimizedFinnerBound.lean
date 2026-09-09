import FinnerOptimization

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

noncomputable def finnerBoundValue {I : Type} [Fintype I] (a b : I → ℝ) : ℝ≥0∞ :=
  ∏ i, (ENNReal.ofReal (1/(1-a i/b i))) ^ b i

/-- The manuscript's optimized Finner functional, defined by its infimum. -/
noncomputable def optimizedFinnerCost {V I : Type} [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) : ℝ≥0∞ :=
  ⨅ b : {b // b ∈ RepeatedEvidence.finnerDomain A a}, finnerBoundValue a b.val

theorem universalCost_le_optimizedFinnerCost {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 < a i) :
    universalCost A a ≤ optimizedFinnerCost A a := by
  apply le_iInf
  intro b
  exact universalCost_le_finner A a b.val ha b.property.1 b.property.2

theorem finnerBoundValue_eq_exp_objective {V I : Type} [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a b : I → ℝ) (ha : ∀ i, 0 < a i)
    (hb : b ∈ RepeatedEvidence.finnerDomain A a) :
    finnerBoundValue a b = ENNReal.ofReal (Real.exp (RepeatedEvidence.finnerObjective a b)) := by
  have he (i : I) : (ENNReal.ofReal (1/(1-a i/b i))) ^ b i =
      ENNReal.ofReal (Real.exp (RepeatedEvidence.finnerTerm (a i) (b i))) := by
    have hb0 := (ha i).trans (hb.1 i)
    have hq : 0 < 1-a i/b i := sub_pos.mpr ((div_lt_one hb0).2 (hb.1 i))
    rw [ENNReal.ofReal_rpow_of_pos (one_div_pos.mpr hq),
      Real.rpow_def_of_pos (one_div_pos.mpr hq), one_div, Real.log_inv]
    congr 2
    unfold RepeatedEvidence.finnerTerm
    ring
  unfold finnerBoundValue RepeatedEvidence.finnerObjective
  simp_rw [he]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),Real.exp_sum]

/-- The infimum defining K_F is achieved by exactly one feasible vector.
No minimizer or compactness conclusion is assumed as a premise. -/
theorem optimizedFinnerCost_unique_attainment {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (hstudy : ∀ i, ∃ v, A v i) (hload : ∀ v, sourceLoad A a v < 1) :
    ∃! b, b ∈ RepeatedEvidence.finnerDomain A a ∧
      finnerBoundValue a b = optimizedFinnerCost A a := by
  obtain ⟨b,⟨hb,hmin⟩,hunique⟩ := RepeatedEvidence.finner_subcritical_unique_optimizer
    A a ha hstudy hload
  have hbound (c : I → ℝ) (hc : c ∈ RepeatedEvidence.finnerDomain A a) :
      finnerBoundValue a b ≤ finnerBoundValue a c := by
    rw [finnerBoundValue_eq_exp_objective A a b ha hb,
      finnerBoundValue_eq_exp_objective A a c ha hc]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hmin hc))
  have heq : finnerBoundValue a b = optimizedFinnerCost A a := by
    apply le_antisymm
    · exact le_iInf fun c => hbound c.val c.property
    · exact iInf_le (fun c : {c // c ∈ RepeatedEvidence.finnerDomain A a} =>
        finnerBoundValue a c.val) ⟨b,hb⟩
  refine ⟨b,⟨hb,heq⟩,?_⟩
  intro c hc
  apply hunique c
  refine ⟨hc.1,?_⟩
  intro d hd
  have hle : finnerBoundValue a c ≤ finnerBoundValue a d := by
    rw [hc.2,← heq]
    exact hbound d hd
  rw [finnerBoundValue_eq_exp_objective A a c ha hc.1,
    finnerBoundValue_eq_exp_objective A a d ha hd] at hle
  exact Real.exp_le_exp.mp ((ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp hle)

theorem optimizedFinnerCost_finite {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (hstudy : ∀ i, ∃ v, A v i) (hload : ∀ v, sourceLoad A a v < 1) :
    optimizedFinnerCost A a ≠ ∞ := by
  obtain ⟨b,⟨hb,heq⟩,_⟩ := optimizedFinnerCost_unique_attainment A a ha hstudy hload
  rw [← heq,finnerBoundValue_eq_exp_objective A a b ha hb]
  exact ENNReal.ofReal_ne_top

end RepeatedEvidenceProbability
