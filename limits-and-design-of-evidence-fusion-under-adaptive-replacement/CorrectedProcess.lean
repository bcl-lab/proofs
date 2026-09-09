import Anytime
import ConditionalFusion

open scoped BigOperators NNReal ENNReal
open Finset Set MeasureTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

def correctedProcess (lam Y : ℕ → Ω → ℝ) (k : ℕ → ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  robustProduct (fun i : Fin n => 1-lam i ω) (fun i : Fin n => lam i ω)
    (fun i : Fin n => Y i ω) (cardinalityAttacks (k n)) (cardinalityAttacks_nonempty (k n))

theorem correctedProcess_nonneg (lam Y : ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (hln : ∀ i ω, 0 ≤ lam i ω) (hl1 : ∀ i ω, lam i ω ≤ 1)
    (hYn : ∀ i ω, 0 ≤ Y i ω) (n : ℕ) (ω : Ω) :
    0 ≤ correctedProcess lam Y k n ω := by
  unfold correctedProcess robustProduct
  apply Finset.le_inf' (cardinalityAttacks_nonempty (k n))
  intro C _
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : i ∈ C
  · simp only [hi,if_true]; exact sub_nonneg.mpr (hl1 i ω)
  · simp only [hi,if_false]
    exact add_nonneg (sub_nonneg.mpr (hl1 i ω)) (mul_nonneg (hln i ω) (hYn i ω))

theorem correctedProcess_measurable (lam Y : ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (hlm : ∀ i, StronglyMeasurable[m0] (lam i))
    (hYm : ∀ i, StronglyMeasurable[m0] (Y i)) (n : ℕ) :
    StronglyMeasurable[m0] (correctedProcess lam Y k n) := by
  have hp (C : Finset (Fin n)) : StronglyMeasurable[m0]
      (fun ω => ∏ i : Fin n, if i ∈ C then 1-lam i ω else 1-lam i ω+lam i ω*Y i ω) := by
    apply Finset.stronglyMeasurable_prod
    intro i _
    by_cases hi : i ∈ C
    · simp only [hi,if_true]; exact stronglyMeasurable_const.sub (hlm i)
    · simp only [hi,if_false]
      exact (stronglyMeasurable_const.sub (hlm i)).add ((hlm i).mul (hYm i))
  have hmin : Continuous (fun v : Finset (Fin n) → ℝ =>
      (cardinalityAttacks (k n)).inf' (cardinalityAttacks_nonempty (k n)) v) :=
    Continuous.finset_inf'_apply _ (fun C _ => continuous_apply C)
  exact (hmin.measurable.comp (measurable_pi_lambda _ (fun C => (hp C).measurable))).stronglyMeasurable

theorem correctedProcess_domination (lam X Y : ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (hln : ∀ i ω, 0 ≤ lam i ω) (hl1 : ∀ i ω, lam i ω ≤ 1)
    (hXn : ∀ i ω, 0 ≤ X i ω)
    (hattack : ∀ n, ∀ᵐ ω ∂μ,
      hamming (fun i : Fin n => X i ω) (fun i : Fin n => Y i ω) ≤ k n) (n : ℕ) :
    correctedProcess lam Y k n ≤ᵐ[μ]
      productProcess (fun i ω => 1-lam i ω+lam i ω*X i ω) n := by
  filter_upwards [hattack n] with ω ha
  let x : Fin n → ℝ := fun i => X i ω
  let y : Fin n → ℝ := fun i => Y i ω
  have hC : differences x y ∈ cardinalityAttacks (k n) :=
    (mem_cardinalityAttacks (k n) _).mpr ha
  have he (i : Fin n) (hi : i ∉ differences x y) : y i = x i := by
    simpa [differences,eq_comm] using hi
  have hh := robustProduct_domination (fun i : Fin n => 1-lam i ω)
    (fun i : Fin n => lam i ω) x y _ (cardinalityAttacks_nonempty (k n)) _ hC
    (fun i => sub_nonneg.mpr (hl1 i ω)) (fun i => hln i ω) (fun i => hXn i ω) he
  change correctedProcess lam Y k n ω ≤ _ at hh
  have heprod := Fin.prod_univ_eq_prod_range (fun i => 1-lam i ω+lam i ω*X i ω) n
  change (∏ i : Fin n, (1-lam i ω+lam i ω*X i ω)) = _ at heprod
  exact hh.trans_eq heprod

/-- Theorem S5: the actual corrected process, with predictable fractions,
has bounded stopping-time validity and the infinite-horizon supremum bound. -/
theorem correctedProcess_anytime (lam X Y : ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (hlm : ∀ i, StronglyMeasurable[ℱ i] (lam i))
    (hXm : ∀ i, StronglyMeasurable[ℱ (i+1)] (X i))
    (hYm : ∀ i, StronglyMeasurable[m0] (Y i))
    (hln : ∀ i ω, 0 ≤ lam i ω) (hl1 : ∀ i ω, lam i ω ≤ 1)
    (hXi : ∀ i, Integrable (X i) μ) (hXn : ∀ i ω, 0 ≤ X i ω)
    (hYn : ∀ i ω, 0 ≤ Y i ω)
    (hc : ∀ i, μ[X i|ℱ i] ≤ᵐ[μ] (1 : Ω → ℝ))
    (hattack : ∀ n, ∀ᵐ ω ∂μ,
      hamming (fun i : Fin n => X i ω) (fun i : Fin n => Y i ω) ≤ k n) :
    (∀ (τ : Ω → ℕ), IsStoppingTime ℱ τ → ∀ N, (∀ ω, τ ω ≤ N) →
      Integrable (stoppedValue (correctedProcess lam Y k) τ) μ ∧
        (∫ ω, stoppedValue (correctedProcess lam Y k) τ ω ∂μ) ≤ 1) ∧
    ∀ a : ℝ, 0 < a →
      μ {ω | ENNReal.ofReal a ≤ ⨆ n, ENNReal.ofReal (correctedProcess lam Y k n ω)} ≤
        ENNReal.ofReal (1/a) := by
  let L := fun i ω => 1-lam i ω+lam i ω*X i ω
  have hM := clean_betting_supermartingale lam X hlm hXm hln hl1 hXi hXn hc
  have hMn := productProcess_nonneg L (fun i ω =>
    add_nonneg (sub_nonneg.mpr (hl1 i ω)) (mul_nonneg (hln i ω) (hXn i ω)))
  have hR := correctedProcess_domination lam X Y k hln hl1 hXn hattack
  have hRmeas := correctedProcess_measurable lam Y k (fun i => (hlm i).mono (ℱ.le i)) hYm
  constructor
  · intro τ hτ N hN
    exact dominated_bounded_stopping hM (productProcess_zero L)
      (fun n => (hRmeas n).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (correctedProcess_nonneg lam Y k hln hl1 hYn n))
      hR τ hτ N hN
  · intro a ha
    apply le_trans _ (ville_supremum hM (productProcess_zero L) hMn a ha)
    apply measure_mono_ae
    have hall := (ae_all_iff).mpr hR
    filter_upwards [hall] with ω hω
    intro hsup
    exact hsup.trans (iSup_mono (fun n => ENNReal.ofReal_le_ofReal (hω n)))

end
end EvidenceFusion
