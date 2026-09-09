import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset
open scoped BigOperators
namespace RepeatedEvidenceProbability

/-- Real false discovery proportion, with denominator one for an empty report. -/
noncomputable def falseDiscoveryProportion {I : Type*} [DecidableEq I]
    (H R : Finset I) : ℝ := ((R ∩ H).card : ℝ) / max (R.card : ℝ) 1

/-- The deterministic inequality behind e-value multiple testing. Self
consistency requires each reported e-value to pass its cardinality threshold. -/
theorem self_consistent_fdp_bound {I : Type*} [Fintype I] [DecidableEq I]
    (H R : Finset I) (E : I → ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hm : 0 < Fintype.card I) (hE : ∀ i ∈ H, 0 ≤ E i)
    (hR : ∀ i ∈ R, (Fintype.card I : ℝ) ≤ α * R.card * E i) :
    falseDiscoveryProportion H R ≤ (α / Fintype.card I) * ∑ i ∈ H, E i := by
  have hm' : (0:ℝ) < Fintype.card I := by exact_mod_cast hm
  have hcoef : 0 ≤ α / Fintype.card I := div_nonneg hα hm'.le
  by_cases hr : R = ∅
  · subst R
    simp only [falseDiscoveryProportion, empty_inter, card_empty, Nat.cast_zero, zero_div]
    exact mul_nonneg hcoef (sum_nonneg hE)
  · have hr0 : 0 < R.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hr)
    have hr1 : (1:ℝ) ≤ R.card := by exact_mod_cast (Nat.succ_le_of_lt hr0)
    have hrc : (0:ℝ) < R.card := lt_of_lt_of_le zero_lt_one hr1
    have hpoint : ∀ i ∈ R ∩ H, 1 / (R.card:ℝ) ≤ α / Fintype.card I * E i := by
      intro i hi
      have hh := hR i (mem_inter.mp hi).1
      apply (div_le_iff₀ hrc).2
      have hh' : (1:ℝ) ≤ (α * R.card * E i) / Fintype.card I :=
        (le_div_iff₀ hm').2 (by simpa using hh)
      convert hh' using 1 <;> ring
    unfold falseDiscoveryProportion
    rw [max_eq_left hr1]
    calc
      ((R ∩ H).card:ℝ) / (R.card:ℝ) = ∑ i ∈ R ∩ H, 1 / (R.card:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ i ∈ R ∩ H, (α / Fintype.card I) * E i := sum_le_sum hpoint
      _ ≤ ∑ i ∈ H, (α / Fintype.card I) * E i := by
        apply sum_le_sum_of_subset_of_nonneg inter_subset_right
        intro i hi _
        exact mul_nonneg hcoef (hE i hi)
      _ = (α / Fintype.card I) * ∑ i ∈ H, E i := (mul_sum _ _ _).symm

noncomputable def passingSet {I : Type*} [Fintype I] (E : I → ℝ) (α : ℝ) (k : Nat) : Finset I := by
  classical
  exact univ.filter (fun i => (Fintype.card I : ℝ) ≤ α * k * E i)

noncomputable def eligibleCounts {I : Type*} [Fintype I] (E : I → ℝ) (α : ℝ) : Finset Nat := by
  classical
  exact (range (Fintype.card I+1)).filter (fun k => k ≤ (passingSet E α k).card)

theorem eligibleCounts_nonempty {I : Type*} [Fintype I] (E : I → ℝ) (α : ℝ) :
    (eligibleCounts E α).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp [eligibleCounts]

noncomputable def eBHCount {I : Type*} [Fintype I] (E : I → ℝ) (α : ℝ) : Nat :=
  (eligibleCounts E α).max' (eligibleCounts_nonempty E α)

/-- The usual step-up rejection set, written using threshold counts instead of
an arbitrary ordering of tied observations. -/
noncomputable def eBHSelection {I : Type*} [Fintype I] (E : I → ℝ) (α : ℝ) : Finset I :=
  if eBHCount E α = 0 then ∅ else passingSet E α (eBHCount E α)

theorem eBHCount_eligible {I : Type*} [Fintype I] (E : I → ℝ) (α : ℝ) :
    eBHCount E α ≤ (passingSet E α (eBHCount E α)).card := by
  classical
  have h := (eligibleCounts E α).max'_mem (eligibleCounts_nonempty E α)
  exact (mem_filter.mp h).2

theorem eBHCount_le_selected {I : Type*} [Fintype I] (E : I → ℝ) (α : ℝ) :
    eBHCount E α ≤ (eBHSelection E α).card := by
  by_cases h : eBHCount E α = 0
  · simp [h]
  · simpa [eBHSelection,h] using eBHCount_eligible E α

/-- The explicitly constructed e-value Benjamini-Hochberg selection satisfies
the threshold condition needed by the expected-error proof. -/
theorem eBH_self_consistent {I : Type*} [Fintype I] (E : I → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (hE : ∀ i, 0 ≤ E i) :
    ∀ i ∈ eBHSelection E α, (Fintype.card I : ℝ) ≤ α * (eBHSelection E α).card * E i := by
  classical
  intro i hi
  by_cases h : eBHCount E α = 0
  · simp [eBHSelection,h] at hi
  · have hi' : i ∈ passingSet E α (eBHCount E α) := by simpa [eBHSelection,h] using hi
    have ht : (Fintype.card I : ℝ) ≤ α * eBHCount E α * E i := (mem_filter.mp hi').2
    apply ht.trans
    apply mul_le_mul_of_nonneg_right _ (hE i)
    apply mul_le_mul_of_nonneg_left _ hα
    exact_mod_cast eBHCount_le_selected E α

end RepeatedEvidenceProbability
