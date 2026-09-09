import ContinuousVille
import QuantileCore

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

theorem cdf_order_of_tail_order (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ t, μ (Ioi t) ≤ ν (Ioi t)) : ∀ t, cdf ν t ≤ cdf μ t := by
  intro t
  have hm := measureReal_add_measureReal_compl (μ:=μ) (measurableSet_Iic (a:=t))
  have hn := measureReal_add_measureReal_compl (μ:=ν) (measurableSet_Iic (a:=t))
  rw [compl_Iic,measureReal_univ_eq_one,← cdf_eq_real] at hm hn
  have ht : μ.real (Ioi t) ≤ ν.real (Ioi t) := ENNReal.toReal_mono (measure_ne_top ν _) (h t)
  linarith

noncomputable def MonitoringModel.logMaximum {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) (ω : model.Ω) : ℝ :=
  Real.log ((model.maximum i ω).toReal)

theorem MonitoringModel.logMaximum_measurable {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) : Measurable (model.logMaximum i) :=
  (model.maximum_measurable i).ennreal_toReal.log

theorem MonitoringModel.logMaximum_source_measurable {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) :
    Measurable[studyInformation A model.sources i] (model.logMaximum i) :=
  (model.maximum_source_measurable i).ennreal_toReal.log

theorem MonitoringModel.maximum_ge_one_ae {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) : ∀ᵐ ω ∂model.μ, 1 ≤ model.maximum i ω := by
  filter_upwards [model.initial i] with ω hω
  have h := le_iSup (fun t : ℝ≥0 => ENNReal.ofReal (model.process i t ω)) 0
  simpa only [hω,ENNReal.ofReal_one] using h

theorem MonitoringModel.maximum_real_pos_ae {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) : ∀ᵐ ω ∂model.μ, 0 < (model.maximum i ω).toReal := by
  filter_upwards [model.maximum_ge_one_ae i,model.maximum_finite_ae i] with ω hω hf
  exact ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hω)) hf

theorem MonitoringModel.maximum_power_eq_exp_log {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) (a : ℝ) :
    ∀ᵐ ω ∂model.μ, model.maximum i ω ^ a = ENNReal.ofReal (Real.exp (a*model.logMaximum i ω)) := by
  filter_upwards [model.maximum_real_pos_ae i,model.maximum_finite_ae i] with ω hp hf
  rw [← ENNReal.ofReal_toReal hf,ENNReal.ofReal_rpow_of_pos hp,Real.rpow_def_of_pos hp]
  simp [MonitoringModel.logMaximum,ENNReal.toReal_ofReal hp.le,mul_comm]

theorem MonitoringModel.cost_eq_log_integral {V I : Type} [Fintype I] {A : V → I → Prop}
    (model : MonitoringModel A) (a : I → ℝ) :
    model.cost a = ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ i, a i*model.logMaximum i ω)) ∂model.μ := by
  have h := (ae_all_iff.mpr (fun i => model.maximum_power_eq_exp_log i (a i)))
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω
  simp_rw [hω]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),Real.exp_sum]

theorem MonitoringModel.logMaximum_tail_order {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) (t : ℝ) :
    model.μ {ω | t < model.logMaximum i ω} ≤ expMeasure 1 (Ioi t) := by
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  by_cases ht : 0 ≤ t
  · have hm : expMeasure 1 (Ioi t) = ENNReal.ofReal (Real.exp (-t)) := by
      rw [← ofReal_measureReal]
      exact congrArg ENNReal.ofReal (exponential_survival_mass (⟨t,ht⟩ : ℝ≥0))
    rw [hm]
    have hv := model.ville_tail i (Real.exp t) (Real.exp_pos t)
    rw [one_div,← Real.exp_neg] at hv
    apply le_trans (measure_mono_ae _) hv
    filter_upwards [model.maximum_real_pos_ae i,model.maximum_finite_ae i] with ω hp hf
    intro hω
    have hreal : Real.exp t < (model.maximum i ω).toReal :=
      (Real.lt_log_iff_exp_lt hp).mp hω
    exact (ENNReal.ofReal_lt_iff_lt_toReal (Real.exp_pos t).le hf).mpr hreal
  · have he : expMeasure 1 (Ioi t) = 1 := by
      apply (mem_ae_iff_prob_eq_one (μ:=expMeasure 1) (measurableSet_Ioi (a:=t))).mp
      filter_upwards [exponential_positive_ae] with z hz
      exact (lt_of_not_ge ht).trans hz
    rw [he]
    exact prob_le_one

theorem MonitoringModel.logMaximum_cdf_order {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) :
    ∀ t, cdf (expMeasure 1) t ≤ cdf (model.μ.map (model.logMaximum i)) t := by
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  haveI : IsProbabilityMeasure (model.μ.map (model.logMaximum i)) :=
    isProbabilityMeasure_map (model.logMaximum_measurable i).aemeasurable
  apply cdf_order_of_tail_order
  intro t
  rw [Measure.map_apply (model.logMaximum_measurable i) measurableSet_Ioi]
  exact model.logMaximum_tail_order i t

end RepeatedEvidenceProbability
