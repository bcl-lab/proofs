import StochasticModel

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

theorem ofReal_ciSup_eq {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hb : BddAbove (range f)) : ENNReal.ofReal (⨆ i, f i) = ⨆ i, ENNReal.ofReal (f i) := by
  have hu : (⨆ i, ENNReal.ofReal (f i)) ≤ ENNReal.ofReal (⨆ i, f i) :=
    iSup_le fun i => ENNReal.ofReal_le_ofReal (le_ciSup hb i)
  have ht : (⨆ i, ENNReal.ofReal (f i)) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  apply le_antisymm _ hu
  rw [ENNReal.ofReal_le_iff_le_toReal ht]
  apply ciSup_le
  intro i
  exact (ENNReal.ofReal_le_iff_le_toReal ht).1 (le_iSup (fun i => ENNReal.ofReal (f i)) i)

theorem exponential_extended_maximum (z : ℝ) :
    (⨆ t : ℝ≥0, ENNReal.ofReal (exponentialSurvival t z)) =
      if 0 < z then ENNReal.ofReal (Real.exp z) else 0 := by
  by_cases hz : 0 < z
  · have hb : BddAbove (range (fun t : ℝ≥0 => exponentialSurvival t z)) := by
      refine ⟨Real.exp z, ?_⟩
      rintro y ⟨t,rfl⟩
      change exponentialSurvival t z ≤ Real.exp z
      by_cases ht : (t:ℝ) < z
      · rw [exponentialSurvival, indicator_of_mem (show z ∈ Ioi (t:ℝ) from ht)]
        exact Real.exp_le_exp.mpr ht.le
      · rw [exponentialSurvival, indicator_of_not_mem (show z ∉ Ioi (t:ℝ) from ht)]
        exact (Real.exp_pos _).le
    rw [if_pos hz, ← ofReal_ciSup_eq _ hb, exponential_running_supremum z hz]
  · rw [if_neg hz]
    apply le_antisymm (iSup_le _) (zero_le _)
    intro t
    have ht : z ∉ Ioi (t:ℝ) := not_lt.mpr ((le_of_not_gt hz).trans t.coe_nonneg)
    simp [exponentialSurvival, indicator_of_not_mem ht]

/-- The actual extended running maximum is measurable, with its null-set
behavior stated explicitly. -/
theorem exponential_extended_maximum_measurable :
    Measurable (fun z => ⨆ t : ℝ≥0, ENNReal.ofReal (exponentialSurvival t z)) := by
  simp_rw [exponential_extended_maximum]
  exact Measurable.ite measurableSet_Ioi Real.measurable_exp.ennreal_ofReal measurable_const

/-- A compatible system concentrating all randomness at a specified source.
Every study using that source uses its exponential survival martingale;
the other studies use the constant martingale one. -/
noncomputable def loadedSourceModel {V I : Type} [DecidableEq V]
    (A : V → I → Prop) [DecidableRel A] (v : V) : MonitoringModel A where
  Ω := ℝ
  ambient := inferInstance
  μ := expMeasure 1
  probability := isProbabilityMeasureExponential (by norm_num)
  sources w := if w = v then inferInstance else ⊥
  sources_le w := by split <;> simp
  independent := by
    letI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
    exact independent_single_source (expMeasure 1) v
  filtration _ := survivalFiltration (fun t : ℝ≥0 => Ioi (t:ℝ))
    (fun _ _ h => Ioi_subset_Ioi h)
  process i := if A v i then exponentialSurvival else fun _ _ => 1
  valid i := by
    letI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
    split
    · exact exponential_survival_martingale.supermartingale
    · exact (martingale_const _ _ (1:ℝ)).supermartingale
  nonnegative i t z := by
    split
    · exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    · exact zero_le_one
  initial i := by
    split
    · exact exponential_initial_ae
    · exact ae_of_all _ (fun _ => rfl)
  right_continuous i z t := by
    split
    · exact exponential_survival_right_continuous z t
    · exact continuousWithinAt_const
  source_measurable i t := by
    split_ifs with hi
    · have hm : Measurable (exponentialSurvival t) :=
        measurable_const.indicator measurableSet_Ioi
      apply hm.mono _ le_rfl
      exact le_iSup_of_le v (le_iSup_of_le hi (by simp))
    · exact measurable_const
  maximum_measurable i := by
    split_ifs
    · exact exponential_extended_maximum_measurable
    · simpa using (measurable_const : Measurable (fun _ : ℝ => (1:ℝ≥0∞)))

noncomputable def sourceLoad {V I : Type} [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (v : V) : ℝ :=
  ∑ i, if A v i then a i else 0

theorem loadedSourceModel_maximum {V I : Type} [DecidableEq V]
    (A : V → I → Prop) [DecidableRel A] (v : V) (i : I) (z : ℝ) (hz : 0 < z) :
    (loadedSourceModel A v).maximum i z =
      if A v i then ENNReal.ofReal (Real.exp z) else 1 := by
  unfold MonitoringModel.maximum loadedSourceModel
  split_ifs with hi
  · simp [hi, exponential_extended_maximum, hz]
  · simp [hi]

theorem loadedSourceModel_product {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (v : V)
    (z : ℝ) (hz : 0 < z) :
    (∏ i, (loadedSourceModel A v).maximum i z ^ a i) =
      ENNReal.ofReal (Real.exp (sourceLoad A a v * z)) := by
  have he : ∀ i, (loadedSourceModel A v).maximum i z ^ a i =
      ENNReal.ofReal (Real.exp ((if A v i then a i else 0)*z)) := by
    intro i
    rw [loadedSourceModel_maximum A v i z hz]
    split_ifs
    · rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, mul_comm]
    · simp
  simp_rw [he]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),
    ← Real.exp_sum, ← Finset.sum_mul]
  rfl

/-- The lower-bound construction has infinite expected product at and above
load one, as an admissible system in the universal definition. -/
theorem loadedSourceModel_cost_infinite {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (v : V)
    (hload : 1 ≤ sourceLoad A a v) : (loadedSourceModel A v).cost a = ∞ := by
  unfold MonitoringModel.cost
  change (∫⁻ z, ∏ i, (loadedSourceModel A v).maximum i z ^ a i ∂expMeasure 1) = ∞
  calc
    _ = ∫⁻ z, ENNReal.ofReal (Real.exp (sourceLoad A a v * z)) ∂expMeasure 1 := by
      apply lintegral_congr_ae
      filter_upwards [exponential_positive_ae] with z hz
      exact loadedSourceModel_product A a v z hz
    _ = ∞ := exponential_supercritical_moment_infinite _ hload

/-- Necessity in Proposition 1, including the load-one boundary. This is a
statement about the universal functional, not a conditional moment premise. -/
theorem universalCost_infinite_of_source_load {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (v : V)
    (hload : 1 ≤ sourceLoad A a v) : universalCost A a = ∞ := by
  apply top_unique
  rw [← loadedSourceModel_cost_infinite A a v hload]
  exact model_cost_le_universal _ a

theorem all_source_loads_lt_one_of_finite_cost {V I : Type} [DecidableEq V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ)
    (hfinite : universalCost A a ≠ ∞) : ∀ v, sourceLoad A a v < 1 := by
  intro v
  by_contra h
  exact hfinite (universalCost_infinite_of_source_load A a v (le_of_not_gt h))

end RepeatedEvidenceProbability
