import QuantileCore

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace RepeatedEvidenceProbability

theorem cdf_continuous_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim]
  have hs : ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) = 0 := by
    rw [← (cdf μ).measure_singleton,measure_cdf]
    exact measure_singleton x
  have hl : Function.leftLim (cdf μ) x = cdf μ x :=
    le_antisymm ((monotone_cdf μ).leftLim_le le_rfl)
      (sub_nonpos.mp (ENNReal.ofReal_eq_zero.mp hs))
  have hr : Function.rightLim (cdf μ) x = cdf μ x :=
    (monotone_cdf μ).continuousWithinAt_Ioi_iff_rightLim_eq.mp
      (((cdf μ).right_continuous x).mono Ioi_subset_Ici_self)
  exact hl.trans hr.symm

theorem cdf_lowerQuantile (μ : Measure ℝ) (hμ : Continuous (cdf μ))
    {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    cdf μ (lowerQuantile μ u) = u := by
  apply le_antisymm _ ((lowerQuantile_le_iff μ hu).mp le_rfl)
  by_contra h
  have hlt : u < cdf μ (lowerQuantile μ u) := lt_of_not_ge h
  have hc : ContinuousWithinAt (cdf μ) (Iio (lowerQuantile μ u)) (lowerQuantile μ u) :=
    hμ.continuousAt.continuousWithinAt
  have hev : ∀ᶠ y in 𝓝[<] (lowerQuantile μ u), u < cdf μ y :=
    hc.eventually (Ioi_mem_nhds hlt)
  have hid : ∀ᶠ y in 𝓝[<] (lowerQuantile μ u), y < lowerQuantile μ u := self_mem_nhdsWithin
  obtain ⟨y,hy,hcy⟩ := (hid.and hev).exists
  exact (hy.trans_le ((lowerQuantile_le_iff μ hu).mpr hcy.le)).false

/-- The probability integral transform, derived from the quantile law. -/
theorem cdf_map_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Continuous (cdf μ)) : μ.map (cdf μ) = uniformRank := by
  calc
    μ.map (cdf μ) = (uniformRank.map (lowerQuantile μ)).map (cdf μ) := by
      rw [lowerQuantile_map]
    _ = uniformRank.map (fun u => cdf μ (lowerQuantile μ u)) := by
      rw [Measure.map_map (monotone_cdf μ).measurable (lowerQuantile_measurable μ)]
      rfl
    _ = uniformRank.map id := by
      apply Measure.map_congr
      filter_upwards [uniformRank_open] with u hu
      exact cdf_lowerQuantile μ hμ hu
    _ = uniformRank := Measure.map_id

theorem lowerQuantile_cdf_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Continuous (cdf μ)) : ∀ᵐ x ∂μ, lowerQuantile μ (cdf μ x) = x := by
  have h : ∀ᵐ u ∂uniformRank,
      lowerQuantile μ (cdf μ (lowerQuantile μ u)) = lowerQuantile μ u := by
    filter_upwards [uniformRank_open] with u hu
    rw [cdf_lowerQuantile μ hμ hu]
  have hm : MeasurableSet {x | lowerQuantile μ (cdf μ x) = x} :=
    measurableSet_eq_fun ((lowerQuantile_measurable μ).comp (monotone_cdf μ).measurable) measurable_id
  have ha := (ae_map_iff (lowerQuantile_measurable μ).aemeasurable hm).mpr h
  simpa only [lowerQuantile_map] using ha

end RepeatedEvidenceProbability
