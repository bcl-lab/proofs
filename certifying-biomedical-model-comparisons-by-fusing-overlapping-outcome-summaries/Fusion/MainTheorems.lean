import Fusion.PartitionNetwork
import Fusion.LaminarFusion
import Fusion.Separation
import Fusion.AUROC

namespace FusionPaper
open Finset

theorem positive_scale_bounds (C D lo t hi : ℝ) (hD : 0 < D) (h : lo ≤ t ∧ t ≤ hi) :
    (C+lo)/D ≤ (C+t)/D ∧ (C+t)/D ≤ (C+hi)/D := by
  exact ⟨div_le_div_of_nonneg_right (add_le_add_left h.1 C) hD.le,
    div_le_div_of_nonneg_right (add_le_add_left h.2 C) hD.le⟩

/-- Theorem 1 with the paper's affine target and positive denominator. -/
theorem theorem1 {n h k : ℕ} (d : Fusion.CountData n h k) (a : Fin n → ℝ)
    (C D : ℝ) (hD : 0 < D) (hne : ∃ y, Fusion.CountFeasible d y) :
    ∃ lo hi : Fin n → ℤ, Fusion.CountFeasible d lo ∧ Fusion.CountFeasible d hi ∧
      ∀ y, FusionPartition.RealCountFeasible d y →
        (C+(∑ i, a i*(lo i : ℝ)))/D ≤ (C+(∑ i, a i*y i))/D ∧
        (C+(∑ i, a i*y i))/D ≤ (C+(∑ i, a i*(hi i : ℝ)))/D := by
  obtain ⟨lo,hi,hlo,hhi,hh⟩ := FusionPartition.two_partition_sharp d a hne
  exact ⟨lo,hi,hlo,hhi,fun y hy => positive_scale_bounds C D _ _ _ hD (hh y hy)⟩

/-- Theorem 2 with the paper's affine target, on finite nonempty cohorts. -/
theorem theorem2 {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : FusionHierarchy.Data ι) (ha : FusionLaminar.Laminar d.A) (hb : FusionLaminar.Laminar d.B)
    (a : ι → ℝ) (C D : ℝ) (hD : 0 < D) (hne : ∃ y, FusionHierarchy.IntegerCounts d y) :
    ∃ lo hi : ι → ℤ, FusionHierarchy.IntegerCounts d lo ∧ FusionHierarchy.IntegerCounts d hi ∧
      ∀ y, FusionHierarchy.RealCounts d y →
        (C+(∑ i, a i*(lo i : ℝ)))/D ≤ (C+(∑ i, a i*y i))/D ∧
        (C+(∑ i, a i*y i))/D ≤ (C+(∑ i, a i*(hi i : ℝ)))/D := by
  obtain ⟨lo,hi,hlo,hhi,hh⟩ := FusionHierarchy.two_laminar_sharp d ha hb a hne
  exact ⟨lo,hi,hlo,hhi,fun y hy => positive_scale_bounds C D _ _ _ hD (hh y hy)⟩

/-- The endpoint statement of Theorem 2 also includes the empty-cohort case. -/
theorem theorem2_all_finite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : FusionHierarchy.Data ι) (ha : FusionLaminar.Laminar d.A) (hb : FusionLaminar.Laminar d.B)
    (a : ι → ℝ) (C D : ℝ) (hD : 0 < D) (hne : ∃ y, FusionHierarchy.IntegerCounts d y) :
    ∃ lo hi : ι → ℤ, FusionHierarchy.IntegerCounts d lo ∧ FusionHierarchy.IntegerCounts d hi ∧
      ∀ y, FusionHierarchy.RealCounts d y →
        (C+(∑ i, a i*(lo i : ℝ)))/D ≤ (C+(∑ i, a i*y i))/D ∧
        (C+(∑ i, a i*y i))/D ≤ (C+(∑ i, a i*(hi i : ℝ)))/D := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    letI := h
    obtain ⟨y,hy⟩ := hne
    exact ⟨y,y,hy,hy,by intros; simp⟩
  | inr h =>
    letI := h
    exact theorem2 d ha hb a C D hD hne

/-- Theorem 3 includes the count/rank construction and exact numeric budget
    declarations in Fusion.Separation. This check specializes only the
    existence of a feasible input attaining the universal adaptive lower bound. -/
theorem theorem3_input_lower (k : ℕ) (p : Fusion.ReviewPolicy (FusionTree.Edge k))
    (hp : FusionTree.NumericPolicyCorrect k p) :
    ∃ y, FusionTree.PositiveCounts k y ∧
      k+1 ≤ FusionTree.runQueries (fun y e => y e) p y :=
  (FusionTree.exact_numeric_budgets k).2.2.2 p hp

end FusionPaper
