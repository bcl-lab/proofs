import CommonSourceCost
import CappedMoments

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

theorem ofReal_minimum (x y : ℝ) :
    ENNReal.ofReal (min x y) = min (ENNReal.ofReal x) (ENNReal.ofReal y) := by
  by_cases h : x ≤ y
  · rw [min_eq_left h,min_eq_left (ENNReal.ofReal_le_ofReal h)]
  · rw [min_eq_right (le_of_not_ge h),min_eq_right (ENNReal.ofReal_le_ofReal (le_of_not_ge h))]

noncomputable def MonitoringModel.clippedMaximum {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (H : ℝ) (i : I) (ω : model.Ω) : ℝ≥0∞ :=
  min (model.maximum i ω) (ENNReal.ofReal H)

noncomputable def MonitoringModel.cappedCost {V I : Type} [Fintype I] {A : V → I → Prop}
    (model : MonitoringModel A) (H : ℝ) (a : I → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∏ i, model.clippedMaximum H i ω ^ a i ∂model.μ

noncomputable def universalCappedCost {V I : Type} [Fintype I]
    (A : V → I → Prop) (H : ℝ) (a : I → ℝ) : ℝ≥0∞ :=
  ⨆ model : MonitoringModel A, model.cappedCost H a

theorem MonitoringModel.clipped_power_moment {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) (H p : ℝ) (hH : 1 ≤ H) (hp : 0 < p) :
    (∫⁻ ω, model.clippedMaximum H i ω ^ p ∂model.μ) ≤
      ENNReal.ofReal (RepeatedEvidence.capMoment H p) := by
  have hreal := ville_tail_capped_moment model.μ (fun ω => (model.maximum i ω).toReal)
    (model.maximum_measurable i).ennreal_toReal.aemeasurable
    (ae_of_all _ (fun _ => ENNReal.toReal_nonneg)) (fun u hu => ?_) H p hH hp
  · convert hreal using 1
    apply lintegral_congr_ae
    filter_upwards [model.maximum_finite_ae i] with ω hω
    rw [← ENNReal.ofReal_rpow_of_nonneg
      (le_min ENNReal.toReal_nonneg (zero_le_one.trans hH)) hp.le,
      ofReal_minimum,ENNReal.ofReal_toReal hω]
    rfl
  · apply le_trans (measure_mono_ae _) (model.ville_tail i u (zero_lt_one.trans_le hu))
    filter_upwards [model.maximum_finite_ae i] with ω hω
    exact (ENNReal.ofReal_lt_iff_lt_toReal (zero_le_one.trans hu) hω).mpr

theorem capMoment_ge_one (H p : ℝ) (hH : 1 ≤ H) (hp : 0 < p) :
    1 ≤ RepeatedEvidence.capMoment H p := by
  letI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have hb : ENNReal.ofReal (1:ℝ) ≤ ENNReal.ofReal (RepeatedEvidence.capMoment H p) := by
    rw [← capped_exponential_moment H p hH]
    calc
      ENNReal.ofReal (1:ℝ) = ∫⁻ _ : ℝ, (1:ℝ≥0∞) ∂expMeasure 1 := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [exponential_positive_ae] with z hz
        have hm : 1 ≤ min (Real.exp z) H := le_min ((Real.one_lt_exp_iff).2 hz).le hH
        have hr := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hm hp.le
        simpa using ENNReal.ofReal_le_ofReal hr
  exact (ENNReal.ofReal_le_ofReal_iff'.1 hb).resolve_right (by norm_num)

/-- Ordinary Holder gives the sharp shared-source ceiling bound. -/
theorem MonitoringModel.cappedCost_le {V I : Type} [Fintype I] {A : V → I → Prop}
    (model : MonitoringModel A) (H : ℝ) (hH : 1 ≤ H) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hT : 0 < ∑ i, a i) :
    model.cappedCost H a ≤ ENNReal.ofReal (RepeatedEvidence.capMoment H (∑ i, a i)) := by
  let T := ∑ i, a i
  let C := RepeatedEvidence.capMoment H T
  have hC : 0 < C := zero_lt_one.trans_le (capMoment_ge_one H T hH hT)
  have hw : (∑ i, a i / T) = 1 := by rw [← Finset.sum_div]; exact div_self hT.ne'
  have hHolder := ENNReal.lintegral_prod_norm_pow_le (μ := model.μ) Finset.univ
    (f := fun i ω => model.clippedMaximum H i ω ^ T)
    (fun i _ => ((model.maximum_measurable i).min measurable_const).aemeasurable.pow_const T)
    hw (fun i _ => div_nonneg (ha i) hT.le)
  have he : ∀ i ω, (model.clippedMaximum H i ω ^ T) ^ (a i/T) =
      model.clippedMaximum H i ω ^ a i := by
    intro i ω
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [hT.ne']
  simp_rw [he] at hHolder
  apply hHolder.trans
  calc
    _ ≤ ∏ i, (ENNReal.ofReal C) ^ (a i/T) := by
      apply Finset.prod_le_prod'
      intro i _
      exact ENNReal.rpow_le_rpow (model.clipped_power_moment i H T hH hT)
        (div_nonneg (ha i) hT.le)
    _ = ENNReal.ofReal C := by
      simp_rw [ENNReal.ofReal_rpow_of_pos hC]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.rpow_pos_of_pos hC _).le),
        ← Real.rpow_sum_of_pos hC,hw,Real.rpow_one]

theorem universalCappedCost_le {V I : Type} [Fintype I]
    (A : V → I → Prop) (H : ℝ) (hH : 1 ≤ H) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hT : 0 < ∑ i, a i) :
    universalCappedCost A H a ≤ ENNReal.ofReal (RepeatedEvidence.capMoment H (∑ i, a i)) := by
  exact iSup_le fun model => model.cappedCost_le H hH a ha hT

theorem loadedSourceModel_cappedCost {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ)
    (v : V) (hv : ∀ i, A v i) (H : ℝ) (hH : 1 ≤ H) :
    (loadedSourceModel A v).cappedCost H a =
      ENNReal.ofReal (RepeatedEvidence.capMoment H (∑ i, a i)) := by
  unfold MonitoringModel.cappedCost
  change (∫⁻ z, ∏ i, (loadedSourceModel A v).clippedMaximum H i z ^ a i ∂expMeasure 1) = _
  rw [← capped_exponential_moment H (∑ i, a i) hH]
  apply lintegral_congr_ae
  filter_upwards [exponential_positive_ae] with z hz
  have he : ∀ i, (loadedSourceModel A v).clippedMaximum H i z =
      ENNReal.ofReal (min (Real.exp z) H) := by
    intro i
    rw [MonitoringModel.clippedMaximum,loadedSourceModel_maximum A v i z hz,
      if_pos (hv i),ofReal_minimum]
  have hpos : 0 < min (Real.exp z) H := lt_min (Real.exp_pos z) (zero_lt_one.trans_le hH)
  simp_rw [he,ENNReal.ofReal_rpow_of_pos hpos]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.rpow_pos_of_pos hpos _).le),
    ← Real.rpow_sum_of_pos hpos]

/-- Complete exact universal capped cost whenever every study shares a source.
This proves the system-A equality in Corollary 3.1 once its common source is supplied. -/
theorem universalCappedCost_common_source {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (v : V) (hv : ∀ i, A v i) (H : ℝ) (hH : 1 ≤ H) (hT : 0 < ∑ i, a i) :
    universalCappedCost A H a = ENNReal.ofReal (RepeatedEvidence.capMoment H (∑ i, a i)) := by
  apply le_antisymm (universalCappedCost_le A H hH a ha hT)
  rw [← loadedSourceModel_cappedCost A a v hv H hH]
  exact le_iSup (fun model : MonitoringModel A => model.cappedCost H a) (loadedSourceModel A v)

end RepeatedEvidenceProbability
