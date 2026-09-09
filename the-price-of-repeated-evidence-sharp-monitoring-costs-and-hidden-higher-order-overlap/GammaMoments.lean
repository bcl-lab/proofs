import ExponentialSurvival

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RepeatedEvidenceProbability

/-- Exponentially tilting a rate-one gamma density changes its rate to 1-p. -/
theorem gamma_tilt_density (q p z : ℝ) (hp : p < 1) :
    gammaPDF q 1 z * ENNReal.ofReal (Real.exp (p*z)) =
      ENNReal.ofReal ((1-p)^(-q)) * gammaPDF q (1-p) z := by
  by_cases hz : 0 ≤ z
  · have hr : 0 < 1-p := sub_pos.mpr hp
    rw [gammaPDF_of_nonneg hz,gammaPDF_of_nonneg hz]
    rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hr (-q)).le]
    rw [← ENNReal.ofReal_mul' (Real.exp_pos (p*z)).le]
    apply congrArg ENNReal.ofReal
    rw [Real.one_rpow,Real.rpow_neg hr.le]
    have he : Real.exp (-z) * Real.exp (p*z) = Real.exp (-((1-p)*z)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [one_mul]
    calc
      1 / Real.Gamma q * z ^ (q-1) * Real.exp (-z) * Real.exp (p*z) =
          1 / Real.Gamma q * z ^ (q-1) * Real.exp (-((1-p)*z)) := by rw [mul_assoc,he]
      _ = ((1-p)^q)⁻¹ * ((1-p)^q / Real.Gamma q * z^(q-1) * Real.exp (-((1-p)*z))) := by
        by_cases hqg : Real.Gamma q = 0
        · simp [hqg]
        · field_simp [hqg,(Real.rpow_pos_of_pos hr q).ne']
          <;> ring
  · simp [gammaPDF_of_neg (lt_of_not_ge hz)]

/-- Exact gamma exponential moment for every positive real shape, not merely
integer Erlang shapes. The density and its normalization are instantiated. -/
theorem gamma_subcritical_moment (q p : ℝ) (hq : 0 < q) (hp : p < 1) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (p*z)) ∂gammaMeasure q 1) =
      ENNReal.ofReal ((1-p)^(-q)) := by
  have hg : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (p*z))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  change (∫⁻ z, ENNReal.ofReal (Real.exp (p*z))
    ∂volume.withDensity (fun x : ℝ => ENNReal.ofReal (gammaPDFReal q 1 x))) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (measurable_gammaPDFReal q 1).ennreal_ofReal
    hg]
  change (∫⁻ z, gammaPDF q 1 z * ENNReal.ofReal (Real.exp (p*z))) = _
  simp_rw [gamma_tilt_density q p _ hp]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_gammaPDF_eq_one hq (sub_pos.mpr hp),mul_one]

end RepeatedEvidenceProbability
