import TailCalibration
import RepeatedEvidence

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RepeatedEvidenceProbability

theorem capped_exponential_density (h p z : ℝ) (hh : 0 ≤ h) :
    exponentialPDF 1 z * ENNReal.ofReal ((min (Real.exp z) (Real.exp h))^p) =
      (Icc 0 h).indicator (fun z => ENNReal.ofReal (Real.exp ((p-1)*z))) z +
      (Ioi h).indicator (fun z => ENNReal.ofReal (Real.exp (p*h-z))) z := by
  by_cases hz : 0 ≤ z
  · by_cases hzh : z ≤ h
    · rw [min_eq_left (Real.exp_le_exp.mpr hzh),
        indicator_of_mem (show z ∈ Icc 0 h from ⟨hz,hzh⟩),
        indicator_of_not_mem (show z ∉ Ioi h from not_lt.mpr hzh),add_zero,
        ← Real.exp_mul,mul_comm z p]
      rw [exponential_tilt_density,indicator_of_mem (show z ∈ Ici 0 from hz)]
    · rw [min_eq_right (Real.exp_le_exp.mpr (le_of_not_ge hzh)),
        indicator_of_not_mem (show z ∉ Icc 0 h from fun hc => hzh hc.2),
        indicator_of_mem (show z ∈ Ioi h from lt_of_not_ge hzh),zero_add,
        exponentialPDF_of_nonneg hz,← Real.exp_mul]
      simp only [one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 2
      ring
  · rw [exponentialPDF_of_neg (lt_of_not_ge hz),zero_mul,
      indicator_of_not_mem (show z ∉ Icc 0 h from fun hc => hz hc.1),
      indicator_of_not_mem (show z ∉ Ioi h from not_lt.mpr ((le_of_not_ge hz).trans hh)),add_zero]

theorem integral_exp_mul_Icc (h c : ℝ) (hh : 0 ≤ h) (hc : c ≠ 0) :
    (∫ z in Icc 0 h, Real.exp (c*z)) = (Real.exp (c*h)-1)/c := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hh,
    intervalIntegral.integral_comp_mul_left _ hc, integral_exp]
  simp [div_eq_mul_inv,mul_comm]

/-- Exact clipped Pareto moment, written first with ceiling exp(h). -/
theorem capped_exponential_moment_log (h p : ℝ) (hh : 0 ≤ h) :
    (∫⁻ z, ENNReal.ofReal ((min (Real.exp z) (Real.exp h))^p) ∂expMeasure 1) =
      ENNReal.ofReal (if p = 1 then 1+h else 1+p*(Real.exp ((p-1)*h)-1)/(p-1)) := by
  have hm : Measurable (fun z : ℝ => ENNReal.ofReal ((min (Real.exp z) (Real.exp h))^p)) :=
    ((Real.measurable_exp.min measurable_const).pow_const p).ennreal_ofReal
  change (∫⁻ z, ENNReal.ofReal ((min (Real.exp z) (Real.exp h))^p)
    ∂volume.withDensity (fun x : ℝ => ENNReal.ofReal (gammaPDFReal 1 1 x))) = _
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (measurable_gammaPDFReal 1 1).ennreal_ofReal hm]
  change (∫⁻ z, exponentialPDF 1 z * ENNReal.ofReal ((min (Real.exp z) (Real.exp h))^p)) = _
  simp_rw [capped_exponential_density h p _ hh]
  have hm1 : Measurable ((Icc 0 h).indicator
      (fun z : ℝ => ENNReal.ofReal (Real.exp ((p-1)*z)))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal.indicator measurableSet_Icc
  rw [lintegral_add_left hm1,
    lintegral_indicator measurableSet_Icc,lintegral_indicator measurableSet_Ioi]
  have hi1 : IntegrableOn (fun z : ℝ => Real.exp ((p-1)*z)) (Icc 0 h) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.integrableOn_Icc
  have he : (fun z : ℝ => Real.exp (p*h-z)) =
      fun z => Real.exp (p*h)*Real.exp ((-1)*z) := by
    funext z
    rw [← Real.exp_add]
    congr 1
    ring
  have hi2 : IntegrableOn (fun z : ℝ => Real.exp (p*h-z)) (Ioi h) := by
    rw [he]
    exact (integrableOn_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) h).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hi1 (ae_of_all _ (fun _ => (Real.exp_pos _).le)),
    ← ofReal_integral_eq_lintegral_ofReal hi2 (ae_of_all _ (fun _ => (Real.exp_pos _).le)),
    ← ENNReal.ofReal_add (integral_nonneg (fun _ => (Real.exp_pos _).le))
      (integral_nonneg (fun _ => (Real.exp_pos _).le))]
  apply congrArg ENNReal.ofReal
  have hu : (∫ z in Ioi h, Real.exp (p*h-z)) = Real.exp ((p-1)*h) := by
    rw [he,integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-1:ℝ) < 0) h]
    simp only [neg_mul,one_mul,div_neg,div_one,neg_neg]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hu]
  split_ifs with hp
  · subst p
    simp [hh]
    ring
  · rw [integral_exp_mul_Icc h (p-1) hh (sub_ne_zero.mpr hp)]
    field_simp [sub_ne_zero.mpr hp]
    <;> ring

/-- The manuscript's g_H(r) is exactly the clipped Pareto moment, including
the logarithmic branch at r=1 and the ceiling H=1. -/
theorem capped_exponential_moment (H p : ℝ) (hH : 1 ≤ H) :
    (∫⁻ z, ENNReal.ofReal ((min (Real.exp z) H)^p) ∂expMeasure 1) =
      ENNReal.ofReal (RepeatedEvidence.capMoment H p) := by
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  have h := capped_exponential_moment_log (Real.log H) p (Real.log_nonneg hH)
  rw [Real.exp_log hHpos] at h
  rw [h]
  apply congrArg ENNReal.ofReal
  unfold RepeatedEvidence.capMoment
  split_ifs
  · rfl
  · rw [Real.rpow_def_of_pos hHpos,mul_comm (Real.log H) (p-1)]

/-- Sharp upper bound for clipped maxima from the Ville tail, for any positive
power. It remains finite even when the uncapped moment diverges. -/
theorem ville_tail_capped_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ℝ)
    (hU : AEMeasurable U μ) (hU0 : ∀ᵐ ω ∂μ, 0 ≤ U ω)
    (htail : ∀ u ≥ 1, μ {ω | u < U ω} ≤ ENNReal.ofReal (1/u))
    (H p : ℝ) (hH : 1 ≤ H) (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal ((min (U ω) H)^p) ∂μ) ≤
      ENNReal.ofReal (RepeatedEvidence.capMoment H p) := by
  rw [← capped_exponential_moment H p hH]
  apply power_moment_le_of_tail_le μ (expMeasure 1) (fun ω => min (U ω) H)
    (fun z => min (Real.exp z) H) (hU.min aemeasurable_const)
    (Real.measurable_exp.min measurable_const).aemeasurable _ _ _ p hp
  · filter_upwards [hU0] with ω hω
    exact le_min hω (zero_le_one.trans hH)
  · exact ae_of_all _ (fun z => le_min (Real.exp_pos z).le (zero_le_one.trans hH))
  · apply clipped_tail_le
    intro u _
    by_cases hu : 1 ≤ u
    · rw [pareto_tail u hu]; exact htail u hu
    · rw [pareto_tail_below_one u (lt_of_not_ge hu)]; exact prob_le_one

end RepeatedEvidenceProbability
