import QuantileCore

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace RepeatedEvidenceProbability

theorem quantile_monotone_tail_domination {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (horder : ∀ x, cdf ν x ≤ cdf (μ.map X) x)
    (Φ : ℝ → ℝ) (hΦ : Measurable Φ) (hmΦ : Monotone Φ) (t : ℝ) :
    μ {ω | t < Φ (X ω)} ≤ uniformRank {u | t < Φ (lowerQuantile ν u)} := by
  haveI : IsProbabilityMeasure (μ.map X) := isProbabilityMeasure_map hX.aemeasurable
  have hs : MeasurableSet {x | t < Φ x} := measurableSet_lt measurable_const hΦ
  calc
    _ = (μ.map X) {x | t < Φ x} := by rw [Measure.map_apply hX hs]; rfl
    _ = (uniformRank.map (lowerQuantile (μ.map X))) {x | t < Φ x} := by rw [lowerQuantile_map]
    _ = uniformRank {u | t < Φ (lowerQuantile (μ.map X) u)} := by
      rw [Measure.map_apply (lowerQuantile_measurable _) hs]
      rfl
    _ ≤ _ := by
      apply measure_mono_ae
      filter_upwards [uniformRank_open] with u hu
      intro ht
      exact ht.trans_le (hmΦ (lowerQuantile_order _ _ horder hu))

end RepeatedEvidenceProbability
