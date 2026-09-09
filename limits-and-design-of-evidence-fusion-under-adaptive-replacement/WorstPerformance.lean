import SupportReduction
import MonotoneCompletion

open scoped BigOperators NNReal
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def affineNN (a : ℝ) (w : ι → ℝ) (x : ι → ℝ≥0) : ℝ := a+∑ i, w i*(x i : ℝ)

def worstValue (F : (ι → ℝ) → ℝ) (x : ι → ℝ≥0) (l : ℕ) : ℝ :=
  sInf {v | ∃ y : ι → ℝ≥0, hamming x y ≤ l ∧ v = F (fun i => (y i : ℝ))}

theorem affineNN_monotone (a : ℝ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Monotone (affineNN a w) := by
  intro x y hxy
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (show (x i : ℝ) ≤ (y i : ℝ) from hxy i) (hw i)

theorem affineNN_erase (a : ℝ) (w : ι → ℝ) (x : ι → ℝ≥0) (C : Finset ι) :
    affineNN a w (eraseCoordinates C x) = a+keptSum w (fun i => (x i : ℝ)) C := by
  unfold affineNN keptSum
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ C <;> simp [eraseCoordinates,hi]

theorem affine_completion (k : ℕ) (a : ℝ) (w : ι → ℝ) (x : ι → ℝ≥0) :
    trimCompletion k (affineNN a w) x =
      robustAffine a w (fun i => (x i : ℝ)) (cardinalityAttacks k) (cardinalityAttacks_nonempty k) := by
  apply le_antisymm
  · obtain ⟨C,hC,he⟩ := Finset.exists_mem_eq_inf' (cardinalityAttacks_nonempty k)
      (keptSum w (fun i => (x i : ℝ)))
    change _ ≤ a+(cardinalityAttacks k).inf' (cardinalityAttacks_nonempty k)
      (keptSum w (fun i => (x i : ℝ)))
    rw [he]
    have hh := Finset.inf'_le (fun C => affineNN a w (eraseCoordinates C x)) hC
    rwa [affineNN_erase] at hh
  · apply Finset.le_inf' (cardinalityAttacks_nonempty k)
    intro C hC
    rw [affineNN_erase]
    exact add_le_add_left (Finset.inf'_le _ hC) a

theorem worstValue_nonempty (F : (ι → ℝ) → ℝ) (x : ι → ℝ≥0) (l : ℕ) :
    {v | ∃ y : ι → ℝ≥0, hamming x y ≤ l ∧ v = F (fun i => (y i : ℝ))}.Nonempty :=
  ⟨F (fun i => (x i : ℝ)),x,by simp [hamming,differences],rfl⟩

theorem worstValue_bddBelow (F : (ι → ℝ) → ℝ)
    (hFn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y) (x : ι → ℝ≥0) (l : ℕ) :
    BddBelow {v | ∃ y : ι → ℝ≥0, hamming x y ≤ l ∧ v = F (fun i => (y i : ℝ))} := by
  refine ⟨0,?_⟩
  rintro v ⟨y,_,rfl⟩
  exact hFn _ (fun i => (y i).coe_nonneg)

theorem worstValue_mono (F G : (ι → ℝ) → ℝ)
    (hFn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y)
    (hdom : ∀ y, (∀ i, 0 ≤ y i) → F y ≤ G y) (x : ι → ℝ≥0) (l : ℕ) :
    worstValue F x l ≤ worstValue G x l := by
  apply le_csInf (worstValue_nonempty G x l)
  rintro v ⟨y,hy,rfl⟩
  exact (csInf_le (worstValue_bddBelow F hFn x l) ⟨y,hy,rfl⟩).trans
    (hdom _ (fun i => (y i).coe_nonneg))

theorem robustAffine_eq_trimmedSum (k : ℕ) (a : ℝ) (w y : ι → ℝ) :
    robustAffine a w y (cardinalityAttacks k) (cardinalityAttacks_nonempty k) =
      a+trimmedSum (fun i => w i*y i) k := by
  rw [trimmedSum_is_min]
  unfold robustAffine
  congr 2
  funext C
  unfold keptSum
  simp

/-- Exact two-budget performance for every affine complete-class member. -/
theorem robustAffine_worst_value (k l : ℕ) (a : ℝ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (x : ι → ℝ≥0) :
    worstValue (fun y => robustAffine a w y (cardinalityAttacks k)
      (cardinalityAttacks_nonempty k)) x l =
      a+trimmedSum (fun i => w i*(x i : ℝ)) (min (Fintype.card ι) (k+l)) := by
  have hf := affineNN_monotone a w hw
  have hh := (trimCompletion_isLeast l _ (monotone_trimCompletion k _ hf) x).csInf_eq
  rw [trimCompletion_composition k l _ hf,affine_completion,
    robustAffine_eq_trimmedSum] at hh
  simpa only [affine_completion,worstValue] using hh

theorem worstValue_constant_one (x : ι → ℝ≥0) (l : ℕ) :
    worstValue (fun _ => 1) x l = 1 := by
  have he : {v | ∃ y : ι → ℝ≥0, hamming x y ≤ l ∧ v = (1 : ℝ)} = {1} := by
    ext v
    constructor
    · rintro ⟨y,_,hv⟩; exact hv
    · intro hv
      exact ⟨x,by simp [hamming,differences],hv⟩
  unfold worstValue
  rw [he,csInf_singleton]

end
end EvidenceFusion
