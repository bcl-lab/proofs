import CorrectedProcess

open scoped BigOperators NNReal ENNReal
open Finset MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {Ω ι : Type} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] {ℱ : Filtration ℕ m0}

def AnytimeValid (R : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : Prop :=
  (∀ (τ : Ω → ℕ), IsStoppingTime ℱ τ → ∀ N, (∀ ω, τ ω ≤ N) →
    Integrable (stoppedValue R τ) μ ∧ (∫ ω, stoppedValue R τ ω ∂μ) ≤ 1) ∧
  ∀ a : ℝ, 0 < a →
    μ {ω | ENNReal.ofReal a ≤ ⨆ n, ENNReal.ofReal (R n ω)} ≤ ENNReal.ofReal (1/a)

/-- Theorem S12, including the second transmission stage. The first layer
proves conditional calibration; the second applies the established corrected
process to the actual transmitted scalar messages. -/
theorem two_layer_anytime (S a : ℕ → Ω → ℝ) (w X Y : ℕ → ι → Ω → ℝ)
    (A : ℕ → Finset (Finset ι)) (hA : ∀ t, (A t).Nonempty)
    (C : ℕ → Ω → Finset ι) (lam Z : ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (ham : ∀ t, StronglyMeasurable[ℱ t] (a t))
    (hwm : ∀ t i, StronglyMeasurable[ℱ t] (w t i))
    (han : ∀ t ω, 0 ≤ a t ω) (hwn : ∀ t i ω, 0 ≤ w t i ω)
    (hnorm : ∀ t ω, a t ω + ∑ i, w t i ω = 1)
    (hXi : ∀ t i, Integrable (X t i) μ)
    (hXn : ∀ t, ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X t i ω)
    (hc : ∀ t i, μ[X t i|ℱ t] ≤ᵐ[μ] (1 : Ω → ℝ))
    (hSm : ∀ t, StronglyMeasurable[ℱ (t+1)] (S t))
    (hSn : ∀ t ω, 0 ≤ S t ω)
    (hC : ∀ t, ∀ᵐ ω ∂μ, C t ω ∈ A t)
    (hclean : ∀ t, ∀ᵐ ω ∂μ, ∀ i, i ∉ C t ω → Y t i ω = X t i ω)
    (hdom : ∀ t, ∀ᵐ ω ∂μ, S t ω ≤ robustAffine (a t ω) (fun i => w t i ω)
      (fun i => Y t i ω) (A t) (hA t))
    (hlm : ∀ t, StronglyMeasurable[ℱ t] (lam t))
    (hZm : ∀ t, StronglyMeasurable[m0] (Z t))
    (hln : ∀ t ω, 0 ≤ lam t ω) (hl1 : ∀ t ω, lam t ω ≤ 1)
    (hZn : ∀ t ω, 0 ≤ Z t ω)
    (htransmission : ∀ n, ∀ᵐ ω ∂μ,
      hamming (fun i : Fin n => S i ω) (fun i : Fin n => Z i ω) ≤ k n) :
    (∀ t, Integrable (S t) μ ∧ μ[S t|ℱ t] ≤ᵐ[μ] (1 : Ω → ℝ)) ∧
      AnytimeValid (correctedProcess lam Z k) ℱ μ := by
  have hS (t : ℕ) : Integrable (S t) μ ∧ μ[S t|ℱ t] ≤ᵐ[μ] (1 : Ω → ℝ) :=
    conditional_robust_fusion (ℱ.le t) (S t) (a t) (w t) (X t) (Y t)
      (A t) (hA t) (C t) (ham t) (hwm t) (han t) (hwn t) (hnorm t)
      (hXi t) (hXn t) (hc t) ((hSm t).mono (ℱ.le (t+1)) |>.aestronglyMeasurable)
      (Filter.Eventually.of_forall (hSn t)) (hC t) (hclean t) (hdom t)
  exact ⟨hS,correctedProcess_anytime lam S Z k hlm hSm hZm hln hl1
    (fun t => (hS t).1) hSn hZn (fun t => (hS t).2) htransmission⟩

end
end EvidenceFusion
