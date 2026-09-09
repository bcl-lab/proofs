import LogMoment
import DelayedMixture
import OrderStatistics

open scoped BigOperators NNReal ENNReal Topology
open Finset Set MeasureTheory ProbabilityTheory Filter Function
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

def delayFraction (s : ℕ) (lam : ℝ) (i : ℕ) : ℝ := if s ≤ i then lam else 0

def maskPrefix {n : ℕ} (s : ℕ) (y : Fin n → ℝ) (i : Fin n) : ℝ :=
  if s ≤ (i : ℕ) then y i else 1

theorem maskPrefix_hamming {n : ℕ} (s : ℕ) (y : Fin n → ℝ) :
    hamming y (maskPrefix s y) ≤ s := by
  have hs : differences y (maskPrefix s y) ⊆ headIndices n s := by
    intro i hi
    have hn : ¬ s ≤ (i : ℕ) := by
      intro his
      simpa [differences,maskPrefix,his] using hi
    simpa [headIndices] using Nat.lt_of_not_ge hn
  exact (Finset.card_le_card hs).trans (by rw [headIndices_card]; exact Nat.min_le_right _ _)

/-- An omitted finite prefix can be charged as a fixed additional budget. -/
theorem delayed_product_lower {n : ℕ} (s k : ℕ) (lam : ℝ) (hl : 0 ≤ lam)
    (hl1 : lam ≤ 1) (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) :
    robustProduct (fun _ => 1-lam) (fun _ => lam) (maskPrefix s y)
      (cardinalityAttacks (k+s)) (cardinalityAttacks_nonempty (k+s)) ≤
    robustProduct (fun i : Fin n => 1-delayFraction s lam i) (fun i : Fin n => delayFraction s lam i) y
      (cardinalityAttacks k) (cardinalityAttacks_nonempty k) := by
  apply Finset.le_inf' (cardinalityAttacks_nonempty k)
  intro C hC
  have hC' : C ∈ cardinalityAttacks (k+s) := (mem_cardinalityAttacks _ _).mpr
    (((mem_cardinalityAttacks k C).mp hC).trans (Nat.le_add_right _ _))
  apply (Finset.inf'_le _ hC').trans
  apply Finset.prod_le_prod
  · intro i _
    split_ifs
    · exact sub_nonneg.mpr hl1
    · apply add_nonneg (sub_nonneg.mpr hl1)
      apply mul_nonneg hl
      unfold maskPrefix
      split_ifs; exact hy i; norm_num
  · intro i _
    by_cases hi : s ≤ (i : ℕ)
    · simp [delayFraction,maskPrefix,hi]
    · by_cases hiC : i ∈ C
      · simp [delayFraction,maskPrefix,hi,hiC,hl]
      · simp [delayFraction,maskPrefix,hi,hiC]

variable {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Delayed components retain the fixed-fraction rate, uniformly over replacements. -/
theorem delayed_fraction_growth_ae (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXn : ∀ i ω, 0 ≤ X i ω)
    (hint : Integrable (fun ω => Real.log (1+X 0 ω)) μ)
    (hindep : Pairwise ((IndepFun · · μ) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (k : ℕ → ℕ) (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (nhds 0))
    (s : ℕ) (lam : ℝ) (hl : 0 ≤ lam) (hl1 : lam < 1) :
    ∀ᵐ ω ∂μ, ∀ c : ℝ, c < (∫ ω, Real.log (1-lam+lam*X 0 ω) ∂μ) →
      ∀ᶠ n : ℕ in atTop, ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) →
        hamming (fun i : Fin n => X i ω) y ≤ k n →
        c ≤ Real.log (robustProduct (fun i : Fin n => 1-delayFraction s lam i)
          (fun i : Fin n => delayFraction s lam i) y
          (cardinalityAttacks (k n)) (cardinalityAttacks_nonempty (k n)))/(n : ℝ) := by
  have hks : Tendsto (fun n => ((k n+s : ℕ) : ℝ)/(n : ℝ)) atTop (nhds 0) := by
    have hs : Tendsto (fun n : ℕ => (s : ℝ)/(n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa [Nat.cast_add,add_div] using hk.add hs
  have hh := fixed_fraction_growth_ae X hXm hXn hint hindep hident (fun n => k n+s)
    hks lam hl hl1
  filter_upwards [hh] with ω hω c hc
  filter_upwards [hω c hc] with n hn y hy ha
  have hym (i : Fin n) : 0 ≤ maskPrefix s y i := by
    unfold maskPrefix; split_ifs; exact hy i; norm_num
  have hat : hamming (fun i : Fin n => X i ω) (maskPrefix s y) ≤ k n+s :=
    (hamming_triangle _ y _).trans (Nat.add_le_add ha (maskPrefix_hamming s y))
  have hb := hn (maskPrefix s y) hym hat
  have hpos := robustProduct_positive (fun _ : Fin n => 1-lam) (fun _ => lam)
    (maskPrefix s y) (cardinalityAttacks (k n+s)) (cardinalityAttacks_nonempty (k n+s))
    (fun _ => sub_pos.mpr hl1) (fun _ => hl) hym
  have hlog := Real.log_le_log hpos (delayed_product_lower s (k n) lam hl hl1.le y hy)
  exact hb.trans (div_le_div_of_nonneg_right hlog (Nat.cast_nonneg n))

end
end EvidenceFusion
