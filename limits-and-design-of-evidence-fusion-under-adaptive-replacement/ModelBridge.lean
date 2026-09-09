import Admissibility

open scoped BigOperators
open Finset Set MeasureTheory
set_option autoImplicit false

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_robustAffine (A : Finset (Finset ι)) (hA : A.Nonempty)
    (a : ℝ) (w : ι → ℝ) : Continuous (fun y => robustAffine a w y A hA) := by
  apply continuous_const.add
  apply Continuous.finset_inf'_apply hA
  intro C _
  unfold keptSum
  apply continuous_finset_sum
  intro i _
  by_cases hi : i ∈ C
  · simp only [hi,if_true]
    exact continuous_const
  · simp only [hi,if_false]
    exact continuous_const.mul (continuous_apply i)

theorem finite_iff_probability_valid (A : Finset (Finset ι)) (hA : A.Nonempty)
    (F : (ι → ℝ) → ℝ) (hn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y) :
    FiniteRobustValid A F ↔ ProbabilityRobustValid A F := by
  rw [complete_class_finite A hA F hn, complete_class_probability A hA F hn]

def ProbabilityAdmissible (A : Finset (Finset ι)) (H : (ι → ℝ) → ℝ) : Prop :=
  ProbabilityRobustValid A H ∧ ∀ G : (ι → ℝ) → ℝ,
    (∀ y, (∀ i, 0 ≤ y i) → 0 ≤ G y) → ProbabilityRobustValid A G →
    (∀ y, (∀ i, 0 ≤ y i) → H y ≤ G y) →
    ∀ y, (∀ i, 0 ≤ y i) → G y = H y

theorem admissible_iff_probability (A : Finset (Finset ι)) (hA : A.Nonempty)
    (H : (ι → ℝ) → ℝ) (hn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ H y) :
    AdmissibleRule A H ↔ ProbabilityAdmissible A H := by
  constructor
  · rintro ⟨hH,hmax⟩
    refine ⟨(finite_iff_probability_valid A hA H hn).mp hH,?_⟩
    intro G hGn hG hdom
    exact hmax G hGn ((finite_iff_probability_valid A hA G hGn).mpr hG) hdom
  · rintro ⟨hH,hmax⟩
    refine ⟨(finite_iff_probability_valid A hA H hn).mpr hH,?_⟩
    intro G hGn hG hdom
    exact hmax G hGn ((finite_iff_probability_valid A hA G hGn).mp hG) hdom

theorem exact_probability_admissibility
    (A : Finset (Finset ι)) (hA : A.Nonempty) (hdown : DownwardClosed A)
    (a : ℝ) (w : ι → ℝ) (ha : 0 ≤ a) (hw : ∀ i, 0 ≤ w i)
    (hn : a + ∑ i, w i = 1) :
    ProbabilityAdmissible A (fun y => robustAffine a w y A hA) ↔
      EmptyMaximalIntersection A w := by
  rw [← admissible_iff_probability A hA _
    (fun y hy => robustAffine_nonneg a w y A hA ha hw hy)]
  exact exact_admissibility A hA hdown a w ha hw hn

theorem compatible_iff_differences (A : Finset (Finset ι))
    (hdown : DownwardClosed A) (x y : ι → ℝ) :
    Compatible A x y ↔ (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ differences x y ∈ A := by
  constructor
  · rintro ⟨hx,hy,C,hC,hxy⟩
    refine ⟨hx,hy,hdown C hC _ ?_⟩
    intro i hi
    by_contra hn
    have he := hxy i hn
    simpa [differences,he] using hi
  · rintro ⟨hx,hy,hd⟩
    refine ⟨hx,hy,differences x y,hd,?_⟩
    intro i hi
    simpa [differences,eq_comm] using hi

end
end EvidenceFusion
