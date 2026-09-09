import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace RepeatedEvidenceProbability

/-- The lower quantile on open probability ranks. Endpoint values are set to
zero and are irrelevant to integration under the uniform law. -/
noncomputable def lowerQuantile (μ : Measure ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo (0:ℝ) 1 then sInf {x | u ≤ cdf μ x} else 0

theorem quantile_upper_set_nonempty (μ : Measure ℝ) {u : ℝ} (hu : u < 1) :
    {x | u ≤ cdf μ x}.Nonempty := by
  obtain ⟨x,hx⟩ := ((tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu)).exists
  exact ⟨x,hx.le⟩

theorem quantile_upper_set_bddBelow (μ : Measure ℝ) {u : ℝ} (hu : 0 < u) :
    BddBelow {x | u ≤ cdf μ x} := by
  obtain ⟨x,hx⟩ := ((tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hu)).exists
  refine ⟨x,?_⟩
  intro y hy
  by_contra h
  have := (monotone_cdf μ) (le_of_not_ge h)
  exact (hx.trans_le (hy.trans this)).false

theorem lowerQuantile_le_iff (μ : Measure ℝ) {u x : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    lowerQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  rw [lowerQuantile,if_pos hu]
  have hne := quantile_upper_set_nonempty μ hu.2
  have hbd := quantile_upper_set_bddBelow μ hu.1
  constructor
  · intro hq
    by_contra h
    have hxu : cdf μ x < u := lt_of_not_ge h
    have hc : ContinuousWithinAt (cdf μ) (Ioi x) x :=
      ((cdf μ).right_continuous x).mono Ioi_subset_Ici_self
    have hev : ∀ᶠ y in 𝓝[>] x, cdf μ y < u := hc.eventually (Iio_mem_nhds hxu)
    have hid : ∀ᶠ y in 𝓝[>] x, x < y := self_mem_nhdsWithin
    obtain ⟨y,hy,hcy⟩ := (hid.and hev).exists
    have hlower : y ≤ sInf {z | u ≤ cdf μ z} := by
      apply le_csInf hne
      intro z hz
      by_contra hyz
      have := (monotone_cdf μ) (le_of_not_ge hyz)
      exact (hcy.trans_le (hz.trans this)).false
    exact (hy.trans_le (hlower.trans hq)).false
  · intro h
    exact csInf_le hbd h

theorem lowerQuantile_monotoneOn (μ : Measure ℝ) :
    MonotoneOn (lowerQuantile μ) (Ioo (0:ℝ) 1) := by
  intro u hu v hv huv
  rw [lowerQuantile_le_iff μ hu]
  exact huv.trans ((lowerQuantile_le_iff μ hv).mp le_rfl)

theorem lowerQuantile_order (μ ν : Measure ℝ)
    (h : ∀ x, cdf ν x ≤ cdf μ x) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    lowerQuantile μ u ≤ lowerQuantile ν u := by
  rw [lowerQuantile_le_iff μ hu]
  exact ((lowerQuantile_le_iff ν hu).mp le_rfl).trans (h _)


theorem lowerQuantile_measurable (μ : Measure ℝ) : Measurable (lowerQuantile μ) := by
  apply measurable_of_Iic
  intro x
  have he : lowerQuantile μ ⁻¹' Iic x =
      (Ioo (0:ℝ) 1 ∩ Iic (cdf μ x)) ∪
        ((Ioo (0:ℝ) 1)ᶜ ∩ {u : ℝ | 0 ≤ x}) := by
    ext u
    by_cases hu : u ∈ Ioo (0:ℝ) 1
    · simp only [mem_preimage,mem_Iic,mem_union,mem_inter_iff,mem_compl_iff,
        mem_setOf_eq,hu,true_and,not_true_eq_false,false_and,or_false]
      exact lowerQuantile_le_iff μ hu
    · simp [lowerQuantile,hu]
  rw [he]
  have hc : MeasurableSet {u : ℝ | 0 ≤ x} := by
    by_cases h : 0 ≤ x <;> simp [h]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (measurableSet_Ioo.compl.inter hc)

noncomputable def uniformRank : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1)

instance uniformRank_probability : IsProbabilityMeasure uniformRank := by
  constructor
  simp [uniformRank,Real.volume_Ioo]

theorem uniformRank_open : ∀ᵐ u ∂uniformRank, u ∈ Ioo (0:ℝ) 1 := by
  exact ae_restrict_mem measurableSet_Ioo

theorem uniformRank_Iic {x : ℝ} (hx : x ≤ 1) :
    uniformRank (Iic x) = ENNReal.ofReal x := by
  rw [uniformRank,restrict_Ioo_eq_restrict_Ioc,Measure.restrict_apply measurableSet_Iic,
    Iic_inter_Ioc_of_le hx,Real.volume_Ioc,sub_zero]

theorem lowerQuantile_map (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    uniformRank.map (lowerQuantile μ) = μ := by
  haveI : IsProbabilityMeasure (uniformRank.map (lowerQuantile μ)) :=
    isProbabilityMeasure_map (lowerQuantile_measurable μ).aemeasurable
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply (lowerQuantile_measurable μ) measurableSet_Iic]
  calc
    uniformRank (lowerQuantile μ ⁻¹' Iic x) = uniformRank (Iic (cdf μ x)) := by
      apply measure_congr
      filter_upwards [uniformRank_open] with u hu
      exact propext (lowerQuantile_le_iff μ hu)
    _ = ENNReal.ofReal (cdf μ x) := uniformRank_Iic (cdf_le_one μ x)
    _ = μ (Iic x) := ofReal_cdf μ x

end RepeatedEvidenceProbability

