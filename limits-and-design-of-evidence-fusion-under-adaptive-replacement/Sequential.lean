import ConditionalMoment
import Cardinality
import Mathlib.Probability.Martingale.OptionalStopping

open scoped BigOperators
open Finset MeasureTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

def productProcess (L : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range n, L i ω

theorem productProcess_zero (L : ℕ → Ω → ℝ) : productProcess L 0 = 1 := by
  funext ω
  simp [productProcess]

theorem productProcess_succ (L : ℕ → Ω → ℝ) (n : ℕ) :
    productProcess L (n+1) = productProcess L n * L n := by
  funext ω
  simp [productProcess,Finset.prod_range_succ]

theorem productProcess_nonneg (L : ℕ → Ω → ℝ)
    (hn : ∀ i ω, 0 ≤ L i ω) (n : ℕ) (ω : Ω) : 0 ≤ productProcess L n ω :=
  Finset.prod_nonneg (fun i _ => hn i ω)

theorem productProcess_adapted (L : ℕ → Ω → ℝ)
    (hm : ∀ i, StronglyMeasurable[ℱ (i+1)] (L i)) : Adapted ℱ (productProcess L) := by
  intro n
  induction n with
  | zero => rw [productProcess_zero]; exact stronglyMeasurable_const
  | succ n ih =>
      have hh := (ih.mono (ℱ.mono (Nat.le_succ n))).mul (hm n)
      rw [productProcess_succ]
      exact hh

theorem productProcess_supermartingale (L : ℕ → Ω → ℝ)
    (hm : ∀ i, StronglyMeasurable[ℱ (i+1)] (L i))
    (hi : ∀ i, Integrable (L i) μ) (hn : ∀ i ω, 0 ≤ L i ω)
    (hc : ∀ i, μ[L i|ℱ i] ≤ᵐ[μ] (1 : Ω → ℝ)) :
    Supermartingale (productProcess L) ℱ μ := by
  have had := productProcess_adapted L hm
  have hint (n : ℕ) : Integrable (productProcess L n) μ := by
    induction n with
    | zero => rw [productProcess_zero]; exact integrable_const (1 : ℝ)
    | succ n ih =>
      have hh := (conditional_mul_integrable (ℱ.le n) (productProcess L n) (L n)
        (had n) ih (hi n) (productProcess_nonneg L hn n) (hn n) (hc n)).1
      rw [productProcess_succ]
      exact hh
  apply supermartingale_nat had hint
  intro n
  have he : productProcess L (n+1) = productProcess L n * L n := by
    funext ω
    simp [productProcess,Finset.prod_range_succ]
  rw [he]
  have hp := condExp_mul_of_stronglyMeasurable_left (μ := μ) (had n)
    (he ▸ hint (n+1)) (hi n)
  filter_upwards [hp,hc n] with ω hp hc
  rw [hp]
  exact (mul_le_mul_of_nonneg_left hc (productProcess_nonneg L hn n ω)).trans_eq (mul_one _)

theorem predictable_betting_factor {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (lam X : Ω → ℝ) (hlm : StronglyMeasurable[m] lam)
    (hln : ∀ ω, 0 ≤ lam ω) (hl1 : ∀ ω, lam ω ≤ 1)
    (hXi : Integrable X μ) (hXn : ∀ ω, 0 ≤ X ω)
    (hc : μ[X|m] ≤ᵐ[μ] (1 : Ω → ℝ)) :
    Integrable (fun ω => 1-lam ω+lam ω*X ω) μ ∧
      μ[(fun ω => 1-lam ω+lam ω*X ω)|m] ≤ᵐ[μ] (1 : Ω → ℝ) := by
  have hlb : ∀ᵐ ω ∂μ, ‖lam ω‖ ≤ (1 : ℝ) := by
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs,abs_of_nonneg (hln ω)] using hl1 ω
  have hli : Integrable lam μ :=
    (integrable_const (1 : ℝ)).mono' (hlm.mono hm |>.aestronglyMeasurable) hlb
  have hlXi : Integrable (lam*X) μ :=
    hXi.bdd_mul' (hlm.mono hm |>.aestronglyMeasurable) hlb
  have hbi : Integrable (fun ω => 1-lam ω) μ := (integrable_const (1 : ℝ)).sub hli
  refine ⟨hbi.add hlXi,?_⟩
  have hsum := condExp_add hbi hlXi m
  have hp := condExp_mul_of_stronglyMeasurable_left (μ := μ) hlm hlXi hXi
  have hb : μ[(fun ω => 1-lam ω)|m] = (fun ω => 1-lam ω) :=
    condExp_of_stronglyMeasurable hm (stronglyMeasurable_const.sub hlm) hbi
  filter_upwards [hsum,hp,hc] with ω hs hp hc
  change μ[((fun ω => 1-lam ω) + lam*X)|m] ω ≤ 1
  rw [hs,hb]
  simp only [Pi.add_apply]
  rw [hp]
  have hh := mul_le_mul_of_nonneg_left hc (hln ω)
  simp only [Pi.mul_apply,Pi.one_apply,mul_one] at *
  linarith

theorem clean_betting_supermartingale (lam X : ℕ → Ω → ℝ)
    (hlm : ∀ i, StronglyMeasurable[ℱ i] (lam i))
    (hXm : ∀ i, StronglyMeasurable[ℱ (i+1)] (X i))
    (hln : ∀ i ω, 0 ≤ lam i ω) (hl1 : ∀ i ω, lam i ω ≤ 1)
    (hXi : ∀ i, Integrable (X i) μ) (hXn : ∀ i ω, 0 ≤ X i ω)
    (hc : ∀ i, μ[X i|ℱ i] ≤ᵐ[μ] (1 : Ω → ℝ)) :
    Supermartingale (productProcess (fun i ω => 1-lam i ω+lam i ω*X i ω)) ℱ μ := by
  apply productProcess_supermartingale
  · intro i
    have hl := (hlm i).mono (ℱ.mono (Nat.le_succ i))
    exact (stronglyMeasurable_const.sub hl).add (hl.mul (hXm i))
  · intro i
    exact (predictable_betting_factor (ℱ.le i) (lam i) (X i) (hlm i)
      (hln i) (hl1 i) (hXi i) (hXn i) (hc i)).1
  · intro i ω
    exact add_nonneg (sub_nonneg.mpr (hl1 i ω)) (mul_nonneg (hln i ω) (hXn i ω))
  · intro i
    exact (predictable_betting_factor (ℱ.le i) (lam i) (X i) (hlm i)
      (hln i) (hl1 i) (hXi i) (hXn i) (hc i)).2

theorem supermartingale_bounded_stopping {M : ℕ → Ω → ℝ}
    (hM : Supermartingale M ℱ μ) (hzero : M 0 = 1)
    (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ τ) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue M τ) μ ∧ (∫ ω, stoppedValue M τ ω ∂μ) ≤ 1 := by
  have hi := hM.neg.integrable_stoppedValue hτ hN
  have he := hM.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0)
    hτ (fun ω => Nat.zero_le _) hN
  have hneg : stoppedValue (-M) τ = -stoppedValue M τ := rfl
  rw [hneg] at hi
  refine ⟨by simpa only [neg_neg] using hi.neg,?_⟩
  rw [stoppedValue_const,hneg] at he
  simp only [Pi.neg_apply,hzero,Pi.one_apply] at he
  simp only [integral_neg] at he
  norm_num at he
  linarith

end
end EvidenceFusion
