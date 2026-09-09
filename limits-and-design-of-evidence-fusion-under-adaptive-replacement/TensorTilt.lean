import InteriorTilt
import Mathlib.MeasureTheory.Integral.Pi

open scoped BigOperators ENNReal
open Set MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {α ι : Type} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]

theorem product_indicator_rectangle (s : ι → Set α) (d : α → ℝ) (x : ι → α) :
    (Set.pi Set.univ s).indicator (fun x => ∏ i, d (x i)) x =
      ∏ i, (s i).indicator d (x i) := by
  by_cases hx : ∀ i, x i ∈ s i
  · simp [Set.mem_pi,hx]
  · have hp : x ∉ Set.pi Set.univ s := by simpa [Set.mem_pi] using hx
    rw [Set.indicator_of_not_mem hp]
    symm
    push_neg at hx
    obtain ⟨i,hi⟩ := hx
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_not_mem hi d)

/-- Finite tensor products commute with an integrable nonnegative density. -/
theorem pi_withDensity (μ : Measure α) [IsProbabilityMeasure μ]
    (d : α → ℝ) (hd : ∀ x, 0 ≤ d x) (hi : Integrable d μ)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (d x)))] :
    (Measure.pi (fun _ : ι => μ.withDensity (fun x => ENNReal.ofReal (d x)))) =
      (Measure.pi (fun _ : ι => μ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, d (x i))) := by
  letI : MeasureSpace α := ⟨μ⟩
  have hprod : Integrable (fun x : ι → α => ∏ i, d (x i)) (Measure.pi (fun _ => μ)) :=
    Integrable.fintype_prod (fun _ => hi)
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  rw [← ofReal_integral_eq_lintegral_ofReal hprod.restrict
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg (fun i _ => hd (x i))))]
  have he : (∫ x in Set.pi Set.univ s, ∏ i, d (x i) ∂Measure.pi (fun _ : ι => μ)) =
      ∏ i, ∫ x in s i, d x ∂μ := by
    rw [← integral_indicator (MeasurableSet.univ_pi hs)]
    simp_rw [product_indicator_rectangle]
    have hh := integral_fintype_prod_eq_prod ι (fun i => (s i).indicator d)
    simpa only [integral_indicator (hs _)] using hh
  rw [he,ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hd))]
  apply Finset.prod_congr rfl
  intro i _
  rw [withDensity_apply _ (hs i),← ofReal_integral_eq_lintegral_ofReal hi.restrict
    (Filter.Eventually.of_forall hd)]

end
end EvidenceFusion
