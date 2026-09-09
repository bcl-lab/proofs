import IndependentQuantiles
import ExponentialQuantile
import AtomlessSums

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

noncomputable def exponentialProduct (J : Type) [Fintype J] : Measure (J → ℝ) :=
  Measure.pi (fun _ => expMeasure 1)

instance exponentialProduct_probability (J : Type) [Fintype J] :
    IsProbabilityMeasure (exponentialProduct J) := by
  letI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : J => expMeasure 1)))

noncomputable def weightedSum {J : Type} [Fintype J] (c : J → ℝ) (x : J → ℝ) : ℝ :=
  ∑ j, c j*x j

theorem weightedSum_measurable {J : Type} [Fintype J] (c : J → ℝ) :
    Measurable (weightedSum c) :=
  Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))

theorem weightedSum_monotone {J : Type} [Fintype J] (c : J → ℝ) (hc : ∀ j, 0 ≤ c j) :
    Monotone (weightedSum c) := by
  intro x y hxy
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hxy j) (hc j))

noncomputable def weightedExponentialLaw {J : Type} [Fintype J] (c : J → ℝ) : Measure ℝ :=
  (exponentialProduct J).map (weightedSum c)

instance weightedExponentialLaw_probability {J : Type} [Fintype J] (c : J → ℝ) :
    IsProbabilityMeasure (weightedExponentialLaw c) :=
  isProbabilityMeasure_map (weightedSum_measurable c).aemeasurable

theorem weightedExponentialLaw_noAtoms {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (c : J → ℝ) (hc : ∀ j, c j ≠ 0) : NoAtoms (weightedExponentialLaw c) := by
  letI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  let X (j : J) (x : J → ℝ) := c j*x j
  have hX : ∀ j, Measurable (X j) :=
    fun j => measurable_const.mul (measurable_pi_apply j)
  have hi : iIndepFun X (exponentialProduct J) :=
    (probability_pi_coordinates_independent (fun _ : J => expMeasure 1)).comp
      (fun j x => c j*x) (fun _ => measurable_const.mul measurable_id)
  let j := Classical.arbitrary J
  have he : (exponentialProduct J).map (X j) = (expMeasure 1).map (fun x => c j*x) := by
    have hm : Measurable (fun x : ℝ => c j*x) := measurable_const.mul measurable_id
    calc
      _ = ((exponentialProduct J).map (fun x => x j)).map (fun x => c j*x) := by
        rw [Measure.map_map hm (measurable_pi_apply j)]
        rfl
      _ = _ := by
        rw [show (exponentialProduct J).map (fun x => x j) = expMeasure 1 from
          probability_pi_coordinate_law (fun _ : J => expMeasure 1) j]
  haveI : NoAtoms ((exponentialProduct J).map (X j)) := by
    rw [he]
    exact noAtoms_map_mul _ _ (hc j)
  exact independent_finite_sum_noAtoms (exponentialProduct J) X hX hi j

theorem weightedExponential_cdf_continuous {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (c : J → ℝ) (hc : ∀ j, c j ≠ 0) : Continuous (cdf (weightedExponentialLaw c)) := by
  letI := weightedExponentialLaw_noAtoms c hc
  exact cdf_continuous_of_noAtoms _

end RepeatedEvidenceProbability
