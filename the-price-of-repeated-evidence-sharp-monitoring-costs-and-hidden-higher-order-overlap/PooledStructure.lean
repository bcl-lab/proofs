import OptimizedFinnerBound

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

/-- `none` is the pooled study; `some j` is the leaf using only source `j`. -/
def pooledUses {J : Type} (v : J) : Option J → Prop
  | none => True
  | some j => v = j

instance pooledUsesDecidable {J : Type} [DecidableEq J] : DecidableRel (@pooledUses J) :=
  fun v i => by cases i <;> simp [pooledUses] <;> infer_instance

def pooledPowers {J : Type} (a₀ : ℝ) (c : J → ℝ) : Option J → ℝ
  | none => a₀
  | some j => c j

theorem pooled_source_load {J : Type} [Fintype J] [DecidableEq J]
    (a₀ : ℝ) (c : J → ℝ) (v : J) :
    sourceLoad pooledUses (pooledPowers a₀ c) v = a₀ + c v := by
  simp [sourceLoad,Fintype.sum_option,pooledUses,pooledPowers]

theorem pooled_cost_finite_iff {J : Type} [Fintype J] [DecidableEq J]
    (a₀ : ℝ) (c : J → ℝ) (ha₀ : 0 < a₀) (hc : ∀ j, 0 < c j) :
    universalCost pooledUses (pooledPowers a₀ c) ≠ ∞ ↔ ∀ j, a₀ + c j < 1 := by
  rw [universalCost_finite_iff _ _ (fun i => by cases i with
    | none => exact ha₀
    | some j => exact hc j)]
  simp_rw [pooled_source_load]

theorem pooled_cost_infinite_of_loaded_leaf {J : Type} [Fintype J] [DecidableEq J]
    (a₀ : ℝ) (c : J → ℝ) (v : J) (hv : 1 ≤ a₀ + c v) :
    universalCost pooledUses (pooledPowers a₀ c) = ∞ := by
  apply universalCost_infinite_of_source_load _ _ v
  simpa only [pooled_source_load] using hv

theorem pooled_leaf_information {J Ω : Type} (sources : J → MeasurableSpace Ω) (j : J) :
    studyInformation pooledUses sources (some j) = sources j := by
  simp [studyInformation,pooledUses]

theorem pooled_all_information {J Ω : Type} (sources : J → MeasurableSpace Ω) :
    studyInformation pooledUses sources none = ⨆ j, sources j := by
  simp [studyInformation,pooledUses]

theorem MonitoringModel.pooled_leaf_maxima_independent {J : Type}
    (model : MonitoringModel (@pooledUses J)) :
    iIndepFun (fun j => model.maximum (some j)) model.μ := by
  rw [iIndepFun_iff_iIndep,iIndep_iff]
  intro s f hf
  apply model.independent.meas_biInter
  intro i hi
  have hm := model.maximum_source_measurable (some i)
  rw [pooled_leaf_information] at hm
  exact (measurable_iff_comap_le.mp hm) _ (hf i hi)

/-- The elementary pooled pattern has no balancing certificate when there
are at least two leaves, even without imposing nonnegativity. -/
theorem pooled_no_balancing_certificate {J : Type} [Fintype J] [DecidableEq J]
    (hJ : 2 ≤ Fintype.card J) :
    ¬ ∃ q : J → ℝ, ∀ i : Option J, (∑ v, if pooledUses v i then q v else 0) = 1 := by
  rintro ⟨q,hq⟩
  have hleaf : ∀ j, q j = 1 := by
    intro j
    simpa [pooledUses] using hq (some j)
  have hp := hq none
  simp only [pooledUses,ite_true,hleaf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hp
  have hcard : (2:ℝ) ≤ Fintype.card J := by exact_mod_cast hJ
  linarith

end RepeatedEvidenceProbability
