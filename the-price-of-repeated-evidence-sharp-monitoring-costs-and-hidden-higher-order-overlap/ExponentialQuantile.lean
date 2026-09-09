import QuantileTransform
import ExponentialSurvival

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace RepeatedEvidenceProbability

instance expOne_noAtoms : NoAtoms (expMeasure 1) := by
  constructor
  intro x
  exact (withDensity_absolutelyContinuous volume (gammaPDF 1 1)) (measure_singleton x)

theorem expOne_cdf (x : ℝ) (hx : 0 ≤ x) :
    cdf (expMeasure 1) x = 1-Real.exp (-x) := by
  change exponentialCDFReal 1 x = _
  rw [exponentialCDFReal_eq (by norm_num),if_pos hx]
  simp

theorem exponential_lowerQuantile {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    lowerQuantile (expMeasure 1) u = -Real.log (1-u) := by
  classical
  have hu0 := hu.1
  have hu1 := hu.2
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have hx : 0 ≤ -Real.log (1-u) := neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have hcdf : cdf (expMeasure 1) (-Real.log (1-u)) = u := by
    rw [expOne_cdf _ hx,neg_neg,Real.exp_log (by linarith : 0 < 1-u)]
    ring
  apply le_antisymm ((lowerQuantile_le_iff _ hu).mpr hcdf.ge)
  have hq : cdf (expMeasure 1) (lowerQuantile (expMeasure 1) u) = u :=
    cdf_lowerQuantile _ (cdf_continuous_of_noAtoms _) hu
  have hq0 : 0 ≤ lowerQuantile (expMeasure 1) u := by
    by_contra h
    have hle : cdf (expMeasure 1) (lowerQuantile (expMeasure 1) u) ≤ cdf (expMeasure 1) 0 :=
      monotone_cdf _ (le_of_not_ge h)
    rw [hq,expOne_cdf 0 le_rfl] at hle
    simp only [neg_zero,Real.exp_zero,sub_self] at hle
    exact (hu.1.trans_le hle).false
  rw [expOne_cdf _ hq0] at hq
  have he : Real.exp (-lowerQuantile (expMeasure 1) u) = 1-u := by linarith
  have hlog := congrArg Real.log he
  rw [Real.log_exp] at hlog
  linarith

theorem exponential_uniform_transform :
    uniformRank.map (fun u : ℝ => -Real.log (1-u)) = expMeasure 1 := by
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  calc
    _ = uniformRank.map (lowerQuantile (expMeasure 1)) := by
      apply Measure.map_congr
      filter_upwards [uniformRank_open] with u hu
      exact (exponential_lowerQuantile hu).symm
    _ = expMeasure 1 := lowerQuantile_map _

end RepeatedEvidenceProbability
