import PooledUpper
import SurvivalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

noncomputable def pooledSurvivalTime {J : Type} [Fintype J] (c : J → ℝ) : (J → ℝ) → ℝ :=
  fun x => -Real.log (1-cdf (weightedExponentialLaw c) (weightedSum c x))

noncomputable def pooledTimes {J : Type} [Fintype J] (c : J → ℝ) : Option J → (J → ℝ) → ℝ
  | none => pooledSurvivalTime c
  | some j => fun x => x j

theorem pooledTimes_measurable {J : Type} [Fintype J] (c : J → ℝ) (i : Option J) :
    Measurable (pooledTimes c i) := by
  cases i with
  | none => exact (measurable_const.sub ((monotone_cdf _).measurable.comp
      (weightedSum_measurable c))).log.neg
  | some j => exact measurable_pi_apply j

theorem pooledTimes_source_measurable {J : Type} [Fintype J] (c : J → ℝ) (i : Option J) :
    Measurable[studyInformation pooledUses coordinateInformation i] (pooledTimes c i) := by
  cases i with
  | none =>
    rw [pooled_all_information]
    exact pooledTimes_measurable c none
  | some j =>
    rw [pooled_leaf_information]
    exact measurable_iff_comap_le.mpr le_rfl

theorem pooledTimes_law {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (c : J → ℝ) (hc : ∀ j, c j ≠ 0) (i : Option J) :
    (exponentialProduct J).map (pooledTimes c i) = expMeasure 1 := by
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  cases i with
  | some j => exact probability_pi_coordinate_law (fun _ : J => expMeasure 1) j
  | none =>
    have hm : Measurable (fun u : ℝ => -Real.log (1-u)) :=
      (measurable_const.sub measurable_id).log.neg
    have hmF := (monotone_cdf (weightedExponentialLaw c)).measurable
    calc
      _ = ((weightedExponentialLaw c).map (cdf (weightedExponentialLaw c))).map
          (fun u : ℝ => -Real.log (1-u)) := by
        rw [Measure.map_map hm hmF]
        change (exponentialProduct J).map (pooledTimes c none) =
          ((exponentialProduct J).map (weightedSum c)).map
            ((fun u : ℝ => -Real.log (1-u)) ∘ cdf (weightedExponentialLaw c))
        rw [Measure.map_map (hm.comp hmF) (weightedSum_measurable c)]
        rfl
      _ = uniformRank.map (fun u : ℝ => -Real.log (1-u)) := by
        rw [cdf_map_uniform _ (weightedExponential_cdf_continuous c hc)]
      _ = expMeasure 1 := exponential_uniform_transform

noncomputable def pooledAttainingModel {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (c : J → ℝ) (hc : ∀ j, c j ≠ 0) : MonitoringModel (@pooledUses J) := by
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  exact survivalModel pooledUses (exponentialProduct J) coordinateInformation
    (fun v => le_iSup (fun w => coordinateInformation w) v)
    ((iIndepFun_iff_iIndep _ _ _).mp
      (probability_pi_coordinates_independent (fun _ : J => expMeasure 1)))
    (pooledTimes c) (pooledTimes_measurable c) (pooledTimes_source_measurable c)
    (pooledTimes_law c hc)

theorem pooledAttainingModel_cost {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ : ℝ) (c : J → ℝ) (hc : ∀ j, c j ≠ 0) :
    (pooledAttainingModel c hc).cost (pooledPowers a₀ c) = pooledQuantileCost a₀ c := by
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp x) *
      ENNReal.ofReal (Real.exp (a₀*(-Real.log (1-cdf (weightedExponentialLaw c) x))))) :=
    Real.measurable_exp.ennreal_ofReal.mul
      (measurable_const.mul (measurable_const.sub (monotone_cdf _).measurable).log.neg).exp.ennreal_ofReal
  calc
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (weightedSum c x)) *
        ENNReal.ofReal (Real.exp (a₀*pooledSurvivalTime c x)) ∂exponentialProduct J := by
      rw [pooledAttainingModel,survivalModel_cost]
      apply lintegral_congr
      intro x
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
      congr 2
      simp [Fintype.sum_option,pooledPowers,pooledTimes,weightedSum,add_comm]
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp x) *
        ENNReal.ofReal (Real.exp (a₀*(-Real.log (1-cdf (weightedExponentialLaw c) x))))
          ∂weightedExponentialLaw c := by
      exact (lintegral_map (μ:=exponentialProduct J) hm (weightedSum_measurable c)).symm
    _ = ∫⁻ u, ENNReal.ofReal (Real.exp (lowerQuantile (weightedExponentialLaw c) u)) *
        ENNReal.ofReal (Real.exp (a₀*(-Real.log (1-cdf (weightedExponentialLaw c)
          (lowerQuantile (weightedExponentialLaw c) u))))) ∂uniformRank := by
      have he := lintegral_map (μ:=uniformRank) hm
        (lowerQuantile_measurable (weightedExponentialLaw c))
      rw [lowerQuantile_map] at he
      exact he
    _ = pooledQuantileCost a₀ c := by
      apply lintegral_congr_ae
      filter_upwards [uniformRank_open] with u hu
      rw [cdf_lowerQuantile _ (weightedExponential_cdf_continuous c hc) hu,
        exponential_lowerQuantile hu]

end RepeatedEvidenceProbability
