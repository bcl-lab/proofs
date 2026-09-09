import EvidenceFusion
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open scoped BigOperators
open Finset MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvidenceFusion
noncomputable section

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The expectation step for arbitrary probability spaces. Integrability of
the dominated statistic is proved, rather than assumed as the conclusion. -/
theorem arbitrary_probability_validity (F : Ω → ℝ) (X : Ω → ι → ℝ)
    (a : ℝ) (w : ι → ℝ)
    (hX : ∀ i, Integrable (fun ω => X ω i) μ)
    (hmean : ∀ i, (∫ ω, X ω i ∂μ) ≤ 1)
    (hw : ∀ i, 0 ≤ w i) (hnorm : a + ∑ i, w i = 1)
    (hFm : AEStronglyMeasurable F μ) (hFn : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hdom : ∀ᵐ ω ∂μ, F ω ≤ a + ∑ i, w i*X ω i) :
    Integrable F μ ∧ (∫ ω, F ω ∂μ) ≤ 1 := by
  have hsum : Integrable (fun ω => ∑ i, w i*X ω i) μ :=
    integrable_finset_sum Finset.univ (fun i _ => (hX i).const_mul (w i))
  have hg : Integrable (fun ω => a + ∑ i, w i*X ω i) μ :=
    (integrable_const a).add hsum
  have hFi : Integrable F μ := by
    apply hg.mono' hFm
    filter_upwards [hFn, hdom] with ω hn hd
    simpa [Real.norm_eq_abs, abs_of_nonneg hn] using hd
  refine ⟨hFi, ?_⟩
  calc
    (∫ ω, F ω ∂μ) ≤ ∫ ω, (a + ∑ i, w i*X ω i) ∂μ :=
      integral_mono_ae hFi hg hdom
    _ = a + ∑ i, w i*(∫ ω, X ω i ∂μ) := by
      rw [integral_add (integrable_const a) hsum,
        integral_finset_sum Finset.univ (fun i _ => (hX i).const_mul (w i))]
      simp_rw [integral_const_mul]
      simp
    _ ≤ 1 := normalized_weight_bound a w _ hw hmean hnorm

/-- The complete sufficiency direction of S1, over arbitrary probability
spaces and outcome-dependent corruption sets. The affine converse is not
assumed or claimed here. -/
theorem robust_fusion_validity (F : Ω → ℝ) (X Y : Ω → ι → ℝ)
    (a : ℝ) (w : ι → ℝ) (A : Finset (Finset ι)) (hA : A.Nonempty)
    (C : Ω → Finset ι)
    (hX : ∀ i, Integrable (fun ω => X ω i) μ)
    (hXn : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X ω i)
    (hmean : ∀ i, (∫ ω, X ω i ∂μ) ≤ 1)
    (hw : ∀ i, 0 ≤ w i) (hnorm : a + ∑ i, w i = 1)
    (hFm : AEStronglyMeasurable F μ) (hFn : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hC : ∀ᵐ ω ∂μ, C ω ∈ A)
    (hclean : ∀ᵐ ω ∂μ, ∀ i, i ∉ C ω → Y ω i = X ω i)
    (hdom : ∀ᵐ ω ∂μ, F ω ≤ robustAffine a w (Y ω) A hA) :
    Integrable F μ ∧ (∫ ω, F ω ∂μ) ≤ 1 := by
  apply arbitrary_probability_validity μ F X a w hX hmean hw hnorm hFm hFn
  filter_upwards [hXn, hC, hclean, hdom] with ω hx hc he hd
  exact hd.trans (robustAffine_le_clean a w (X ω) (Y ω) A hA (C ω) hc hw hx he)

end
end EvidenceFusion
