import FinnerSources

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem probability_pi_coordinate_law {V : Type} [Fintype V]
    (μ : V → Measure ℝ) [∀ v, IsProbabilityMeasure (μ v)] (v : V) :
    (Measure.pi μ).map (fun x => x v) = μ v := by
  classical
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply v) hs]
  have he : (fun x : V → ℝ => x v) ⁻¹' s =
      univ.pi (fun w => if w = v then s else univ) := by
    ext x
    simp only [mem_preimage,mem_pi,mem_univ,true_implies]
    constructor
    · intro h w
      split_ifs with hw
      · simpa [hw] using h
      · trivial
    · intro h
      simpa using h v
  rw [he,Measure.pi_pi]
  simp only [apply_ite,measure_univ]
  simp

theorem probability_pi_coordinates_independent {V : Type} [Fintype V]
    (μ : V → Measure ℝ) [∀ v, IsProbabilityMeasure (μ v)] :
    iIndepFun (fun v (x : V → ℝ) => x v) (Measure.pi μ) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun v => (measurable_pi_apply v).aemeasurable)]
  simp_rw [probability_pi_coordinate_law]
  exact Measure.map_id

end RepeatedEvidenceProbability
