import PooledStructure
import PooledDistribution
import QuantileComparison
import Rearrangement
import LogMaximum

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

noncomputable def pooledQuantileCost {J : Type} [Fintype J] (a₀ : ℝ) (c : J → ℝ) : ℝ≥0∞ :=
  ∫⁻ u, ENNReal.ofReal (Real.exp (lowerQuantile (weightedExponentialLaw c) u)) *
    ENNReal.ofReal (Real.exp (a₀*lowerQuantile (expMeasure 1) u)) ∂uniformRank

theorem MonitoringModel.pooled_leaf_log_independent {J : Type}
    (model : MonitoringModel (@pooledUses J)) :
    iIndepFun (fun j => model.logMaximum (some j)) model.μ := by
  exact model.pooled_leaf_maxima_independent.comp (fun _ x => Real.log x.toReal)
    (fun _ => measurable_id.ennreal_toReal.log)

theorem MonitoringModel.pooled_leaf_statistic_tail {J : Type} [Fintype J]
    (model : MonitoringModel (@pooledUses J)) (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) (s : ℝ) :
    model.μ {ω | s < Real.exp (weightedSum c (fun j => model.logMaximum (some j) ω))} ≤
      uniformRank {u | s < Real.exp (lowerQuantile (weightedExponentialLaw c) u)} := by
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have h := independent_quantile_tail_domination model.μ
    (fun j => model.logMaximum (some j)) (fun j => model.logMaximum_measurable (some j))
    model.pooled_leaf_log_independent (fun _ => expMeasure 1)
    (fun j => model.logMaximum_cdf_order (some j))
    (fun x => Real.exp (weightedSum c x)) (weightedSum_measurable c).exp
    (Real.exp_monotone.comp (weightedSum_monotone c hc)) s
  have hs : MeasurableSet {x : ℝ | s < Real.exp x} := measurableSet_lt measurable_const Real.measurable_exp
  apply h.trans_eq
  calc
    _ = (weightedExponentialLaw c) {x : ℝ | s < Real.exp x} := by
      rw [weightedExponentialLaw,Measure.map_apply (weightedSum_measurable c) hs]
      rfl
    _ = uniformRank {u | s < Real.exp (lowerQuantile (weightedExponentialLaw c) u)} := by
      have he := Measure.map_apply (μ:=uniformRank)
        (lowerQuantile_measurable (weightedExponentialLaw c)) hs
      rw [lowerQuantile_map] at he
      exact he

theorem MonitoringModel.pooled_cost_upper {J : Type} [Fintype J]
    (model : MonitoringModel (@pooledUses J)) (a₀ : ℝ) (c : J → ℝ)
    (ha₀ : 0 ≤ a₀) (hc : ∀ j, 0 ≤ c j) :
    model.cost (pooledPowers a₀ c) ≤ pooledQuantileCost a₀ c := by
  let f : model.Ω → ℝ := fun ω => Real.exp (weightedSum c (fun j => model.logMaximum (some j) ω))
  let g : model.Ω → ℝ := fun ω => Real.exp (a₀*model.logMaximum none ω)
  let F : ℝ → ℝ := fun u => Real.exp (lowerQuantile (weightedExponentialLaw c) u)
  let G : ℝ → ℝ := fun u => Real.exp (a₀*lowerQuantile (expMeasure 1) u)
  have hf : Measurable f := ((weightedSum_measurable c).comp
    (measurable_pi_iff.mpr (fun j => model.logMaximum_measurable (some j)))).exp
  have hg : Measurable g := (measurable_const.mul (model.logMaximum_measurable none)).exp
  have hF : Measurable F := (lowerQuantile_measurable _).exp
  have hG : Measurable G := (measurable_const.mul (lowerQuantile_measurable _)).exp
  have hmF : MonotoneOn F (Ioo (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.exp_le_exp.mpr (lowerQuantile_monotoneOn _ hu hv huv)
  have hmG : MonotoneOn G (Ioo (0:ℝ) 1) := by
    intro u hu v hv huv
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (lowerQuantile_monotoneOn _ hu hv huv) ha₀)
  have htF : ∀ s > 0, model.μ {x | s < f x} ≤ uniformRank {u | s < F u} :=
    fun s _ => model.pooled_leaf_statistic_tail c hc s
  have htG : ∀ t > 0, model.μ {x | t < g x} ≤ uniformRank {u | t < G u} := by
    intro t _
    haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
    exact quantile_monotone_tail_domination model.μ (model.logMaximum none)
      (model.logMaximum_measurable none) (expMeasure 1) (model.logMaximum_cdf_order none)
      (fun x => Real.exp (a₀*x)) (measurable_const.mul measurable_id).exp
      (fun x y hxy => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxy ha₀)) t
  have h := comonotone_product_upper model.μ f g F G hf hg hF hG hmF hmG htF htG
  have he : model.cost (pooledPowers a₀ c) =
      ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (g ω) ∂model.μ := by
    rw [model.cost_eq_log_integral]
    apply lintegral_congr
    intro ω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
    congr 2
    simp [Fintype.sum_option,pooledPowers,weightedSum,f,g,add_comm]
  exact he.le.trans h

theorem pooled_universal_cost_upper {J : Type} [Fintype J]
    (a₀ : ℝ) (c : J → ℝ) (ha₀ : 0 ≤ a₀) (hc : ∀ j, 0 ≤ c j) :
    universalCost pooledUses (pooledPowers a₀ c) ≤ pooledQuantileCost a₀ c :=
  iSup_le (fun model => model.pooled_cost_upper a₀ c ha₀ hc)

end RepeatedEvidenceProbability
