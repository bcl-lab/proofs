import ContinuousVille
import UniversalDivergence
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

/-- The lower-bound model also attains the exact finite exponential moment. -/
theorem loadedSourceModel_cost_subcritical {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (v : V)
    (hload : sourceLoad A a v < 1) :
    (loadedSourceModel A v).cost a = ENNReal.ofReal (1/(1-sourceLoad A a v)) := by
  unfold MonitoringModel.cost
  change (∫⁻ z, ∏ i, (loadedSourceModel A v).maximum i z ^ a i ∂expMeasure 1) = _
  calc
    _ = ∫⁻ z, ENNReal.ofReal (Real.exp (sourceLoad A a v*z)) ∂expMeasure 1 := by
      apply lintegral_congr_ae
      filter_upwards [exponential_positive_ae] with z hz
      exact loadedSourceModel_product A a v z hz
    _ = _ := exponential_subcritical_moment _ hload

/-- Ordinary Holder supplies a universal finite upper bound when the total
power is below one, for every source pattern and every admissible process. -/
theorem MonitoringModel.cost_le_of_total_power {V I : Type} [Fintype I]
    {A : V → I → Prop} (model : MonitoringModel A) (a : I → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hT : 0 < ∑ i, a i) (hT1 : (∑ i, a i) < 1) :
    model.cost a ≤ ENNReal.ofReal (1/(1-∑ i, a i)) := by
  let T := ∑ i, a i
  let C : ℝ := 1/(1-T)
  have hC : 0 < C := one_div_pos.mpr (sub_pos.mpr hT1)
  have hw : (∑ i, a i / T) = 1 := by rw [← Finset.sum_div]; exact div_self hT.ne'
  have hHolder := ENNReal.lintegral_prod_norm_pow_le (μ := model.μ) Finset.univ
    (f := fun i ω => model.maximum i ω ^ T)
    (fun i _ => (model.maximum_measurable i).aemeasurable.pow_const T)
    hw (fun i _ => div_nonneg (ha i) hT.le)
  have he : ∀ i ω, (model.maximum i ω ^ T) ^ (a i/T) = model.maximum i ω ^ a i := by
    intro i ω
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp [hT.ne']
  simp_rw [he] at hHolder
  change model.cost a ≤ ENNReal.ofReal C
  apply hHolder.trans
  calc
    _ ≤ ∏ i, (ENNReal.ofReal C) ^ (a i/T) := by
      apply Finset.prod_le_prod'
      intro i _
      exact ENNReal.rpow_le_rpow (model.maximum_power_moment i T hT hT1)
        (div_nonneg (ha i) hT.le)
    _ = ENNReal.ofReal C := by
      simp_rw [ENNReal.ofReal_rpow_of_pos hC]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.rpow_pos_of_pos hC _).le),
        ← Real.rpow_sum_of_pos hC,hw,Real.rpow_one]

theorem universalCost_le_of_total_power {V I : Type} [Fintype I]
    (A : V → I → Prop) (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hT : 0 < ∑ i, a i) (hT1 : (∑ i, a i) < 1) :
    universalCost A a ≤ ENNReal.ofReal (1/(1-∑ i, a i)) := by
  apply iSup_le
  intro model
  exact model.cost_le_of_total_power a ha hT hT1

/-- Complete exact universal cost for any network containing a source used
by every study, in the finite regime. This includes the single-study case. -/
theorem universalCost_common_source_subcritical {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (v : V) (hv : ∀ i, A v i) (hT : 0 < ∑ i, a i) (hT1 : (∑ i, a i) < 1) :
    universalCost A a = ENNReal.ofReal (1/(1-∑ i, a i)) := by
  apply le_antisymm (universalCost_le_of_total_power A a ha hT hT1)
  have hl : sourceLoad A a v = ∑ i, a i := by simp [sourceLoad,hv]
  have hc := loadedSourceModel_cost_subcritical A a v (by simpa [hl] using hT1)
  rw [hl] at hc
  rw [← hc]
  exact model_cost_le_universal _ a

/-- The exact value includes divergence at the boundary T=1. -/
theorem universalCost_common_source {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 ≤ a i)
    (v : V) (hv : ∀ i, A v i) (hT : 0 < ∑ i, a i) :
    universalCost A a =
      if (∑ i, a i) < 1 then ENNReal.ofReal (1/(1-∑ i, a i)) else ∞ := by
  split_ifs with hT1
  · exact universalCost_common_source_subcritical A a ha v hv hT hT1
  · apply universalCost_infinite_of_source_load A a v
    simpa [sourceLoad,hv] using le_of_not_gt hT1

end RepeatedEvidenceProbability
