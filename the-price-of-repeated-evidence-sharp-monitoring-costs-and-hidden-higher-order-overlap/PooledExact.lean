import PooledAttainment

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

/-- Theorem 4: the actual universal cost equals the quantile optimum. -/
theorem pooled_exact_cost {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ : ℝ) (c : J → ℝ) (ha₀ : 0 < a₀) (hc : ∀ j, 0 < c j) :
    universalCost pooledUses (pooledPowers a₀ c) = pooledQuantileCost a₀ c := by
  apply le_antisymm (pooled_universal_cost_upper a₀ c ha₀.le (fun j => (hc j).le))
  rw [← pooledAttainingModel_cost a₀ c (fun j => (hc j).ne')]
  exact model_cost_le_universal _ _

theorem pooled_quantile_formula {J : Type} [Fintype J] (a₀ : ℝ) (c : J → ℝ) :
    pooledQuantileCost a₀ c = ∫⁻ u in Ioo (0:ℝ) 1,
      ENNReal.ofReal (Real.exp (lowerQuantile (weightedExponentialLaw c) u) * (1-u)^(-a₀)) := by
  apply lintegral_congr_ae
  filter_upwards [uniformRank_open] with u hu
  rw [exponential_lowerQuantile hu,← ENNReal.ofReal_mul (Real.exp_pos _).le,
    Real.rpow_def_of_pos (sub_pos.mpr hu.2)]
  congr 3
  ring

theorem pooled_survival_formula {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ : ℝ) (c : J → ℝ) (ha₀ : 0 < a₀) (hc : ∀ j, 0 < c j) :
    universalCost pooledUses (pooledPowers a₀ c) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (weightedSum c x) *
        (1-cdf (weightedExponentialLaw c) (weightedSum c x))^(-a₀)) ∂exponentialProduct J := by
  let φ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp x *
    (1-cdf (weightedExponentialLaw c) x)^(-a₀))
  have hm : Measurable φ := (Real.measurable_exp.mul
    ((measurable_const.sub (monotone_cdf _).measurable).pow_const _)).ennreal_ofReal
  have he := lintegral_map (μ:=uniformRank) hm
    (lowerQuantile_measurable (weightedExponentialLaw c))
  rw [lowerQuantile_map] at he
  have hq : pooledQuantileCost a₀ c = ∫⁻ x, φ x ∂weightedExponentialLaw c := by
    rw [he,pooled_quantile_formula]
    apply lintegral_congr_ae
    filter_upwards [uniformRank_open] with u hu
    dsimp [φ]
    rw [cdf_lowerQuantile _ (weightedExponential_cdf_continuous c (fun j => (hc j).ne')) hu]
  rw [pooled_exact_cost a₀ c ha₀ hc,hq]
  exact lintegral_map hm (weightedSum_measurable c)

theorem pooled_quantile_finite_iff {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ : ℝ) (c : J → ℝ) (ha₀ : 0 < a₀) (hc : ∀ j, 0 < c j) :
    pooledQuantileCost a₀ c ≠ ∞ ↔ ∀ j, a₀+c j < 1 := by
  rw [← pooled_exact_cost a₀ c ha₀ hc]
  exact pooled_cost_finite_iff a₀ c ha₀ hc

theorem pooled_universal_attained {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ : ℝ) (c : J → ℝ) (ha₀ : 0 < a₀) (hc : ∀ j, 0 < c j) :
    ∃ model : MonitoringModel (@pooledUses J),
      model.cost (pooledPowers a₀ c) = universalCost pooledUses (pooledPowers a₀ c) := by
  refine ⟨pooledAttainingModel c (fun j => (hc j).ne'),?_⟩
  rw [pooledAttainingModel_cost,pooled_exact_cost a₀ c ha₀ hc]

end RepeatedEvidenceProbability
