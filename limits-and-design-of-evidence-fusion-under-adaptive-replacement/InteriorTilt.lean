import LogMoment
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open scoped BigOperators NNReal ENNReal Topology
open Finset Set MeasureTheory ProbabilityTheory Filter Function Metric
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem expected_log_hasDerivAt (X : Ω → ℝ) (hXm : Measurable X)
    (hXn : ∀ ω, 0 ≤ X ω) (hint : Integrable (fun ω => Real.log (1+X ω)) μ)
    (lam : ℝ) (hl : 0 < lam) (hl1 : lam < 1) :
    Integrable (fun ω => (X ω-1)/(1-lam+lam*X ω)) μ ∧
    HasDerivAt (fun t => ∫ ω, Real.log (1-t+t*X ω) ∂μ)
      (∫ ω, (X ω-1)/(1-lam+lam*X ω) ∂μ) lam := by
  let eps := min lam (1-lam)/2
  have he : 0 < eps := div_pos (lt_min hl (by linarith)) (by norm_num)
  have hleft : 2*eps ≤ lam := by dsimp [eps]; linarith [min_le_left lam (1-lam)]
  have hright : 2*eps ≤ 1-lam := by dsimp [eps]; linarith [min_le_right lam (1-lam)]
  have hball (t : ℝ) (ht : t ∈ Metric.ball lam eps) : t ∈ Set.Icc eps (1-eps) := by
    have hh : |t-lam| < eps := by simpa [Metric.mem_ball,Real.dist_eq] using ht
    have hlr := abs_lt.mp hh
    constructor <;> linarith
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (F' := fun t ω =>
    (X ω-1)/(1-t+t*X ω)) (bound := fun _ => 1/eps) he
  · filter_upwards [] with t
    exact (measurable_const.add (measurable_const.mul hXm)).log.aestronglyMeasurable
  · exact log_factor_integrable X hXm hXn hint lam hl.le hl1
  · exact ((hXm.sub_const 1).div (measurable_const.add (measurable_const.mul hXm))).aestronglyMeasurable
  · filter_upwards [] with ω t ht
    have hb := hball t ht
    simpa [Real.norm_eq_abs,abs_div] using
      log_factor_derivative_bound (X ω) t eps (hXn ω) he hb.1 hb.2
  · exact integrable_const _
  · filter_upwards [] with ω t ht
    have hb := hball t ht
    exact log_factor_hasDerivAt (X ω) t (hXn ω) (by linarith [hb.1]) (by linarith [hb.2])

theorem interior_log_optimum_derivative_zero (X : Ω → ℝ) (hXm : Measurable X)
    (hXn : ∀ ω, 0 ≤ X ω) (hint : Integrable (fun ω => Real.log (1+X ω)) μ)
    (lam : ℝ) (hl : 0 < lam) (hl1 : lam < 1)
    (hmax : IsMaxOn (fun t => ∫ ω, Real.log (1-t+t*X ω) ∂μ) (Set.Ioo 0 1) lam) :
    Integrable (fun ω => (X ω-1)/(1-lam+lam*X ω)) μ ∧
      (∫ ω, (X ω-1)/(1-lam+lam*X ω) ∂μ) = 0 := by
  obtain ⟨hi,hd⟩ := expected_log_hasDerivAt X hXm hXn hint lam hl hl1
  exact ⟨hi,(hmax.isLocalMax (Ioo_mem_nhds hl hl1)).hasDerivAt_eq_zero hd⟩

/-- General probability-space tilt identities at an interior optimum. -/
theorem general_tilt_identities (X : Ω → ℝ) (hXn : ∀ ω, 0 ≤ X ω)
    (lam : ℝ) (hl : 0 ≤ lam) (hl1 : lam < 1)
    (hi : Integrable (fun ω => (X ω-1)/(1-lam+lam*X ω)) μ)
    (hz : (∫ ω, (X ω-1)/(1-lam+lam*X ω) ∂μ) = 0) :
    Integrable (fun ω => 1/(1-lam+lam*X ω)) μ ∧
    Integrable (fun ω => X ω/(1-lam+lam*X ω)) μ ∧
    (∫ ω, 1/(1-lam+lam*X ω) ∂μ) = 1 ∧
    (∫ ω, X ω/(1-lam+lam*X ω) ∂μ) = 1 := by
  let D := fun ω => (X ω-1)/(1-lam+lam*X ω)
  have hp (ω : Ω) : 1-lam+lam*X ω ≠ 0 :=
    (add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg hl (hXn ω))).ne'
  have h1 : (fun ω => 1/(1-lam+lam*X ω)) = (fun ω => 1-lam*D ω) := by
    funext ω; dsimp [D]; field_simp [hp ω]; ring
  have h2 : (fun ω => X ω/(1-lam+lam*X ω)) = (fun ω => 1+(1-lam)*D ω) := by
    funext ω; dsimp [D]; field_simp [hp ω]; ring
  rw [h1,h2]
  refine ⟨(integrable_const (1 : ℝ)).sub (hi.const_mul lam),
    (integrable_const (1 : ℝ)).add (hi.const_mul (1-lam)),?_,?_⟩
  · rw [integral_sub (integrable_const _) (hi.const_mul lam),integral_const_mul]
    simp [D,hz]
  · rw [integral_add (integrable_const _) (hi.const_mul (1-lam)),integral_const_mul]
    simp [D,hz]

def reciprocalTilt (μ : Measure Ω) (X : Ω → ℝ) (lam : ℝ) : Measure Ω :=
  μ.withDensity (fun ω => ENNReal.ofReal (1/(1-lam+lam*X ω)))

/-- The reciprocal likelihood tilt is a probability measure under which the
clean evidence variable has mean exactly one. -/
theorem interior_tilt_probability_mean_one (X : Ω → ℝ) (hXm : Measurable X)
    (hXn : ∀ ω, 0 ≤ X ω) (hint : Integrable (fun ω => Real.log (1+X ω)) μ)
    (lam : ℝ) (hl : 0 < lam) (hl1 : lam < 1)
    (hmax : IsMaxOn (fun t => ∫ ω, Real.log (1-t+t*X ω) ∂μ) (Set.Ioo 0 1) lam) :
    IsProbabilityMeasure (reciprocalTilt μ X lam) ∧
      Integrable X (reciprocalTilt μ X lam) ∧ (∫ ω, X ω ∂reciprocalTilt μ X lam) = 1 := by
  obtain ⟨hDi,hDz⟩ := interior_log_optimum_derivative_zero X hXm hXn hint lam hl hl1 hmax
  obtain ⟨h1i,h2i,h1,h2⟩ := general_tilt_identities X hXn lam hl.le hl1 hDi hDz
  have hd (ω : Ω) : 0 ≤ 1/(1-lam+lam*X ω) := by
    apply div_nonneg (by norm_num)
    exact add_nonneg (by linarith) (mul_nonneg hl.le (hXn ω))
  have hdm : Measurable (fun ω => ENNReal.ofReal (1/(1-lam+lam*X ω))) :=
    (measurable_const.div (measurable_const.add (measurable_const.mul hXm))).ennreal_ofReal
  have hdt : ∀ᵐ ω ∂μ, ENNReal.ofReal (1/(1-lam+lam*X ω)) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have he : (fun ω => (ENNReal.ofReal (1/(1-lam+lam*X ω))).toReal • X ω) =
      (fun ω => X ω/(1-lam+lam*X ω)) := by
    funext ω
    rw [ENNReal.toReal_ofReal (hd ω),smul_eq_mul]
    ring
  refine ⟨⟨?_⟩,?_,?_⟩
  · change μ.withDensity _ Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal h1i (Filter.Eventually.of_forall hd),h1]
    norm_num
  · rw [reciprocalTilt,integrable_withDensity_iff_integrable_smul' hdm hdt,he]
    exact h2i
  · rw [reciprocalTilt,integral_withDensity_eq_integral_toReal_smul hdm hdt X]
    change (∫ ω, ((fun ω => (ENNReal.ofReal (1/(1-lam+lam*X ω))).toReal • X ω) ω) ∂μ) = 1
    rw [he]
    exact h2

end
end EvidenceFusion
