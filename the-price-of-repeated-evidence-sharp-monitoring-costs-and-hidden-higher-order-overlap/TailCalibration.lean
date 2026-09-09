import ExponentialSurvival
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RepeatedEvidenceProbability

/-- Tail domination implies domination of every positive power moment, allowing
infinite integrals. This is the layer-cake step used for monitored maxima. -/
theorem power_moment_le_of_tail_le {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) (f : Ω → ℝ) (g : Ξ → ℝ)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hg0 : ∀ᵐ x ∂ν, 0 ≤ g x)
    (htail : ∀ t > 0, μ {x | t < f x} ≤ ν {x | t < g x})
    (p : ℝ) (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂ν := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ hf0 hf hp,
    lintegral_rpow_eq_lintegral_meas_lt_mul ν hg0 hg hp]
  apply mul_le_mul_left'
  apply lintegral_mono_ae
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0:ℝ)))] with t ht
  exact mul_le_mul_right' (htail t ht) _

theorem pareto_tail (u : ℝ) (hu : 1 ≤ u) :
    expMeasure 1 {z : ℝ | u < Real.exp z} = ENNReal.ofReal (1/u) := by
  letI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have hpos : 0 < u := zero_lt_one.trans_le hu
  have he : {z : ℝ | u < Real.exp z} = Ioi (Real.log u) := by
    ext z
    exact (Real.log_lt_iff_lt_exp hpos).symm
  rw [he, ← ofReal_measureReal]
  have ht := exponential_survival_mass (⟨Real.log u, Real.log_nonneg hu⟩ : ℝ≥0)
  change (expMeasure 1).real (Ioi (Real.log u)) = Real.exp (-Real.log u) at ht
  rw [ht,Real.exp_neg,Real.exp_log hpos,one_div]

theorem pareto_tail_below_one (u : ℝ) (hu : u < 1) :
    expMeasure 1 {z : ℝ | u < Real.exp z} = 1 := by
  letI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  apply (mem_ae_iff_prob_eq_one (measurableSet_lt measurable_const Real.measurable_exp)).1
  filter_upwards [exponential_positive_ae] with z hz
  exact hu.trans ((Real.one_lt_exp_iff).2 hz)

/-- The sharp single-maximum calibration from the Ville tail bound.
The tail bound is an explicit input to this intermediate theorem. -/
theorem ville_tail_power_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → ℝ)
    (hU : AEMeasurable U μ) (hU0 : ∀ᵐ ω ∂μ, 0 ≤ U ω)
    (htail : ∀ u ≥ 1, μ {ω | u < U ω} ≤ ENNReal.ofReal (1/u))
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂μ) ≤ ENNReal.ofReal (1/(1-p)) := by
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (Real.exp z ^ p) ∂expMeasure 1 := by
      apply power_moment_le_of_tail_le μ (expMeasure 1) U Real.exp hU
        Real.measurable_exp.aemeasurable hU0 (ae_of_all _ (fun z => (Real.exp_pos z).le)) _ p hp
      intro u _
      by_cases hu : 1 ≤ u
      · rw [pareto_tail u hu]; exact htail u hu
      · rw [pareto_tail_below_one u (lt_of_not_ge hu)]
        exact prob_le_one
    _ = ENNReal.ofReal (1/(1-p)) := by
      simp_rw [← Real.exp_mul, mul_comm _ p]
      exact exponential_subcritical_moment p hp1

/-- Clipping preserves tail domination, including the finite ceiling itself. -/
theorem clipped_tail_le {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) (f : Ω → ℝ) (g : Ξ → ℝ) (H : ℝ)
    (h : ∀ t > 0, μ {x | t < f x} ≤ ν {x | t < g x}) :
    ∀ t > 0, μ {x | t < min (f x) H} ≤ ν {x | t < min (g x) H} := by
  intro t ht
  by_cases hH : t < H
  · simpa [lt_min_iff, hH] using h t ht
  · simp [lt_min_iff, hH]

end RepeatedEvidenceProbability
