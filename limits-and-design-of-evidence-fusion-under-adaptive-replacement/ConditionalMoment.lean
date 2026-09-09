import Probability
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

open scoped BigOperators
open MeasureTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}

/-- A nonnegative predictable multiplier preserves integrability when the
conditional mean of the other factor is at most one. The unbounded multiplier
is handled by monotone convergence of its bounded truncations. -/
theorem conditional_mul_integrable (hm : m ≤ m0) (f g : Ω → ℝ)
    (hfm : StronglyMeasurable[m] f) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfn : ∀ ω, 0 ≤ f ω) (hgn : ∀ ω, 0 ≤ g ω)
    (hcond : μ[g|m] ≤ᵐ[μ] (1 : Ω → ℝ)) :
    Integrable (f*g) μ ∧ (∫ ω, f ω*g ω ∂μ) ≤ ∫ ω, f ω ∂μ := by
  let u : ℕ → Ω → ℝ := fun n ω => min (f ω) (n : ℝ)
  have hum (n : ℕ) : StronglyMeasurable[m] (u n) :=
    (hfm.measurable.min measurable_const).stronglyMeasurable
  have hun (n : ℕ) (ω : Ω) : 0 ≤ u n ω := le_min (hfn ω) (Nat.cast_nonneg n)
  have hub (n : ℕ) : ∀ᵐ ω ∂μ, ‖u n ω‖ ≤ (n : ℝ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hun n ω)]
    exact min_le_right _ _
  have hui (n : ℕ) : Integrable (u n) μ :=
    (integrable_const (n : ℝ)).mono' (hum n |>.mono hm |>.aestronglyMeasurable) (hub n)
  have hi (n : ℕ) : Integrable (fun ω => u n ω*g ω) μ :=
    hgi.bdd_mul' (hum n |>.mono hm |>.aestronglyMeasurable) (hub n)
  have hbound (n : ℕ) : (∫ ω, u n ω*g ω ∂μ) ≤ ∫ ω, f ω ∂μ := by
    have hp := condExp_mul_of_stronglyMeasurable_left (μ := μ) (hum n) (hi n) hgi
    have hc : μ[u n*g|m] ≤ᵐ[μ] u n := by
      filter_upwards [hp,hcond] with ω he hg
      rw [he]
      exact (mul_le_mul_of_nonneg_left hg (hun n ω)).trans_eq (mul_one _)
    calc
      (∫ ω, u n ω*g ω ∂μ) = ∫ ω, μ[u n*g|m] ω ∂μ := (integral_condExp hm).symm
      _ ≤ ∫ ω, u n ω ∂μ := integral_mono_ae integrable_condExp (hui n) hc
      _ ≤ ∫ ω, f ω ∂μ := integral_mono (hui n) hfi (fun ω => min_le_left _ _)
  have hsup (ω : Ω) : (⨆ n, ENNReal.ofReal (u n ω*g ω)) = ENNReal.ofReal (f ω*g ω) := by
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (hgn ω))
    · obtain ⟨n,hn⟩ := exists_nat_ge (f ω)
      exact le_iSup_of_le n (by simp [u,min_eq_left hn])
  have hlin : (∫⁻ ω, ENNReal.ofReal (f ω*g ω) ∂μ) ≤ ENNReal.ofReal (∫ ω, f ω ∂μ) := by
    simp_rw [← hsup]
    rw [lintegral_iSup' (fun n => (hi n).aemeasurable.ennreal_ofReal)]
    · apply iSup_le
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal (hi n)
        (Filter.Eventually.of_forall (fun ω => mul_nonneg (hun n ω) (hgn ω)))]
      exact ENNReal.ofReal_le_ofReal (hbound n)
    · filter_upwards [] with ω n j hnj
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_min_left _ (Nat.cast_le.mpr hnj)) (hgn ω))
  have hfg : Integrable (f*g) μ := by
    refine ⟨hfi.1.mul hgi.1,?_⟩
    change HasFiniteIntegral (fun ω => f ω*g ω) μ
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall (fun ω => mul_nonneg (hfn ω) (hgn ω)))]
    exact hlin.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hfg,?_⟩
  change Integrable (fun ω => f ω*g ω) μ at hfg
  rw [← ofReal_integral_eq_lintegral_ofReal hfg
    (Filter.Eventually.of_forall (fun ω => mul_nonneg (hfn ω) (hgn ω)))] at hlin
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg hfn)).mp hlin

end
end EvidenceFusion
