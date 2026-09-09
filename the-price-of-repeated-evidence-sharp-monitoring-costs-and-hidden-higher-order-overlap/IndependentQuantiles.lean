import QuantileCore
import IndependentCoordinates

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

noncomputable def uniformCube (J : Type) [Fintype J] : Measure (J → ℝ) :=
  Measure.pi (fun _ => uniformRank)

instance uniformCube_probability (J : Type) [Fintype J] : IsProbabilityMeasure (uniformCube J) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : J => uniformRank)))

theorem uniformCube_open (J : Type) [Fintype J] :
    ∀ᵐ u ∂uniformCube J, ∀ j, u j ∈ Ioo (0:ℝ) 1 := by
  rw [ae_all_iff]
  intro j
  have h := uniformRank_open
  rw [← probability_pi_coordinate_law (fun _ : J => uniformRank) j] at h
  exact (ae_map_iff (measurable_pi_apply j).aemeasurable measurableSet_Ioo).mp h

theorem coordinate_quantile_law {J : Type} [Fintype J] (ν : J → Measure ℝ)
    [∀ j, IsProbabilityMeasure (ν j)] (j : J) :
    (uniformCube J).map (fun u => lowerQuantile (ν j) (u j)) = ν j := by
  calc
    _ = ((uniformCube J).map (fun u => u j)).map (lowerQuantile (ν j)) := by
      rw [Measure.map_map (lowerQuantile_measurable _) (measurable_pi_apply j)]
      rfl
    _ = uniformRank.map (lowerQuantile (ν j)) := by
      rw [show (uniformCube J).map (fun u => u j) = uniformRank from
        probability_pi_coordinate_law (fun _ : J => uniformRank) j]
    _ = ν j := lowerQuantile_map (ν j)

theorem quantile_joint_law {J : Type} [Fintype J] (ν : J → Measure ℝ)
    [∀ j, IsProbabilityMeasure (ν j)] :
    (uniformCube J).map (fun u j => lowerQuantile (ν j) (u j)) = Measure.pi ν := by
  have hi := (probability_pi_coordinates_independent (fun _ : J => uniformRank)).comp
    (fun j => lowerQuantile (ν j)) (fun j => lowerQuantile_measurable (ν j))
  have hm : ∀ j, Measurable (fun u : J → ℝ => lowerQuantile (ν j) (u j)) :=
    fun j => (lowerQuantile_measurable _).comp (measurable_pi_apply j)
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hm j).aemeasurable)).mp hi
  change (uniformCube J).map (fun u j => lowerQuantile (ν j) (u j)) =
    Measure.pi (fun j => (uniformCube J).map (fun u => lowerQuantile (ν j) (u j))) at h
  simpa only [coordinate_quantile_law] using h

/-- Independent quantile coupling preserves every increasing measurable
statistic's tail order, for arbitrary finite collections of real marginals. -/
theorem independent_quantile_tail_domination {J Ω : Type} [Fintype J]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : J → Ω → ℝ) (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (ν : J → Measure ℝ) [∀ j, IsProbabilityMeasure (ν j)]
    (horder : ∀ j x, cdf (ν j) x ≤ cdf (μ.map (X j)) x)
    (Φ : (J → ℝ) → ℝ) (hΦ : Measurable Φ) (hmΦ : Monotone Φ) (t : ℝ) :
    μ {ω | t < Φ (fun j => X j ω)} ≤
      (Measure.pi ν) {x | t < Φ x} := by
  letI : ∀ j, IsProbabilityMeasure (μ.map (X j)) :=
    fun j => isProbabilityMeasure_map (hX j).aemeasurable
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hX j).aemeasurable)).mp hi
  have hmS : MeasurableSet {x | t < Φ x} := measurableSet_lt measurable_const hΦ
  calc
    _ = (μ.map (fun ω j => X j ω)) {x | t < Φ x} := by
      rw [Measure.map_apply (measurable_pi_iff.mpr hX) hmS]
      rfl
    _ = (Measure.pi (fun j => μ.map (X j))) {x | t < Φ x} := by rw [hmap]
    _ = (uniformCube J).map (fun u j => lowerQuantile (μ.map (X j)) (u j))
        {x | t < Φ x} := by rw [quantile_joint_law]
    _ ≤ (uniformCube J).map (fun u j => lowerQuantile (ν j) (u j))
        {x | t < Φ x} := by
      have hm₁ : Measurable (fun u : J → ℝ => fun j => lowerQuantile (μ.map (X j)) (u j)) :=
        measurable_pi_iff.mpr (fun j => (lowerQuantile_measurable _).comp (measurable_pi_apply j))
      have hm₂ : Measurable (fun u : J → ℝ => fun j => lowerQuantile (ν j) (u j)) :=
        measurable_pi_iff.mpr (fun j => (lowerQuantile_measurable _).comp (measurable_pi_apply j))
      rw [Measure.map_apply hm₁ hmS,Measure.map_apply hm₂ hmS]
      apply measure_mono_ae
      filter_upwards [uniformCube_open J] with u hu
      intro hx
      exact hx.trans_le (hmΦ (fun j => lowerQuantile_order _ _ (horder j) (hu j)))
    _ = (Measure.pi ν) {x | t < Φ x} := by rw [quantile_joint_law]

end RepeatedEvidenceProbability
