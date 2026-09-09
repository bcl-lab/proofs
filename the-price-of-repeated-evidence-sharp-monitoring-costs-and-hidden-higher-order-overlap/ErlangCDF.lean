import ErlangCalculus

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem gammaPDF_integrable (q r : ℝ) (hq : 0 < q) (hr : 0 < r) :
    Integrable (gammaPDFReal q r) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_gammaPDFReal q r).aestronglyMeasurable
    (ae_of_all _ (fun x => gammaPDFReal_nonneg hq hr x))).mp
  change (∫⁻ x, gammaPDF q r x) ≠ ∞
  rw [lintegral_gammaPDF_eq_one hq hr]
  exact ENNReal.one_ne_top

theorem gamma_cdf_zero (q r : ℝ) (hq : 0 < q) (hr : 0 < r) :
    cdf (gammaMeasure q r) 0 = 0 := by
  change gammaCDFReal q r 0 = 0
  rw [gammaCDFReal_eq_integral hq hr,integral_Iic_eq_integral_Iio]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
  change x < 0 at hx
  simp [gammaPDFReal,not_le.mpr hx]

theorem erlangDensity_continuous (n : ℕ) : Continuous (erlangDensity n) := by
  exact ((continuous_id.pow n).mul (Real.continuous_exp.comp continuous_id.neg)).div_const _

theorem erlang_cdf_formula (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    cdf (gammaMeasure (n+1) 1) t = 1-Real.exp (-t)*erlangPolynomial n t := by
  have hn : (0:ℝ) < n+1 := by positivity
  have hp := gammaPDF_integrable (n+1) 1 hn (by norm_num)
  have hdiff := intervalIntegral.integral_Iic_sub_Iic
    (hp.integrableOn (s:=Iic (0:ℝ))) (hp.integrableOn (s:=Iic t))
  have hzero : (∫ x in Iic (0:ℝ), gammaPDFReal (n+1) 1 x) = 0 := by
    rw [← gammaCDFReal_eq_integral hn (by norm_num)]
    exact gamma_cdf_zero _ _ hn (by norm_num)
  rw [hzero,sub_zero] at hdiff
  change gammaCDFReal (n+1) 1 t = _
  rw [gammaCDFReal_eq_integral hn (by norm_num),hdiff]
  have he : (∫ x in (0:ℝ)..t, gammaPDFReal (n+1) 1 x) = ∫ x in (0:ℝ)..t, erlangDensity n x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 ≤ x := (by simpa [uIcc_of_le ht] using hx : x ∈ Icc 0 t).1
    exact gammaPDF_erlang n x hx0
  rw [he,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => erlang_cdf_derivative n x) ((erlangDensity_continuous n).intervalIntegrable 0 t)]
  simp [erlangPolynomial_zero]

end RepeatedEvidenceProbability
