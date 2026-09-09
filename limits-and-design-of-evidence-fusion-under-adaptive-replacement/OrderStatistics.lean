import SparseTrimming
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

def headIndices (n r : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < r)

theorem headIndices_card (n r : ℕ) : (headIndices n r).card = min n r := by
  by_cases hr : r < n
  · have he : headIndices n r = Finset.Iio (⟨r,hr⟩ : Fin n) := by
      ext i; simp [headIndices,Fin.lt_iff_val_lt_val]
    simp [he,Nat.min_eq_right hr.le]
  · have he : headIndices n r = Finset.univ := by
      ext i; simp [headIndices,lt_of_lt_of_le i.isLt (Nat.le_of_not_gt hr)]
    simp [he,Nat.min_eq_left (Nat.le_of_not_gt hr)]

theorem largestSum_sorted {n : ℕ} (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i)
    (hsort : Antitone z) (r : ℕ) :
    largestSum z r = ∑ i ∈ headIndices n r, z i := by
  apply le_antisymm
  · apply Finset.sup'_le (cardinalityAttacks_nonempty r)
    intro C hC
    have hCr : C.card ≤ r := (mem_cardinalityAttacks r C).mp hC
    by_cases hr : r < n
    · let t := z ⟨r,hr⟩
      let e := fun i : Fin n => if (i : ℕ) < r then z i-t else 0
      have hen (i : Fin n) : 0 ≤ e i := by
        dsimp [e]
        split_ifs with hi
        · exact sub_nonneg.mpr (hsort (show i ≤ ⟨r,hr⟩ from Nat.le_of_lt hi))
        · exact le_rfl
      have hze (i : Fin n) : z i ≤ t+e i := by
        dsimp [e]
        split_ifs with hi
        · linarith
        · simpa using hsort (show (⟨r,hr⟩ : Fin n) ≤ i from Nat.le_of_not_gt hi)
      have hsum := Finset.sum_le_sum (fun i (_ : i ∈ C) => hze i)
      rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at hsum
      have heup : ∑ i ∈ C, e i ≤ ∑ i, e i := Finset.sum_le_univ_sum_of_nonneg hen
      have heq : (∑ i, e i) = (∑ i ∈ headIndices n r, z i) - (r : ℝ)*t := by
        have hh : (∑ i, e i) = ∑ i ∈ headIndices n r, (z i-t) := by
          simp only [e,headIndices,Finset.sum_filter]
        rw [hh,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,
          headIndices_card,Nat.min_eq_right hr.le]
      have hCt : (C.card : ℝ)*t ≤ (r : ℝ)*t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hCr) (hz ⟨r,hr⟩)
      linarith
    · have heq : headIndices n r = Finset.univ := by
        ext i; simp [headIndices,lt_of_lt_of_le i.isLt (Nat.le_of_not_gt hr)]
      rw [heq]
      exact Finset.sum_le_univ_sum_of_nonneg hz
  · exact Finset.le_sup' (fun C => ∑ i ∈ C, z i)
      ((mem_cardinalityAttacks r _).mpr (by rw [headIndices_card]; exact Nat.min_le_right _ _))

theorem largestSum_comp_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (σ : Equiv.Perm ι) (r : ℕ) :
    largestSum (fun i => z (σ i)) r ≤ largestSum z r := by
  apply Finset.sup'_le (cardinalityAttacks_nonempty r)
  intro C hC
  have hmap : C.map σ.toEmbedding ∈ cardinalityAttacks r := by
    rw [mem_cardinalityAttacks,Finset.card_map]
    exact (mem_cardinalityAttacks r C).mp hC
  have hh := Finset.le_sup' (fun B => ∑ i ∈ B, z i) hmap
  simpa only [Finset.sum_map,Equiv.toEmbedding_apply] using hh

theorem largestSum_permutation {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (σ : Equiv.Perm ι) (r : ℕ) :
    largestSum (fun i => z (σ i)) r = largestSum z r := by
  apply le_antisymm (largestSum_comp_le z σ r)
  simpa only [Equiv.apply_symm_apply] using largestSum_comp_le (fun i => z (σ i)) σ.symm r

def descendingPermutation {n : ℕ} (z : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => -z i)

theorem descendingPermutation_antitone {n : ℕ} (z : Fin n → ℝ) :
    Antitone (fun i => z (descendingPermutation z i)) := by
  intro i j hij
  have hh := Tuple.monotone_sort (fun i => -z i) hij
  simpa using hh

/-- `largestSum` equals the ordinary sum of decreasing order statistics,
including budgets exceeding the dimension and ties. -/
theorem largestSum_order_statistics {n : ℕ} (z : Fin n → ℝ) (hz : ∀ i, 0 ≤ z i) (r : ℕ) :
    largestSum z r = ∑ i ∈ headIndices n r, z (descendingPermutation z i) := by
  rw [← largestSum_permutation z (descendingPermutation z) r]
  exact largestSum_sorted _ (fun i => hz _) (descendingPermutation_antitone z) r

def trimmedSum {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → ℝ) (r : ℕ) : ℝ :=
  (∑ i, z i) - largestSum z r

theorem keptSum_unit_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (C : Finset ι) :
    keptSum (fun _ => 1) z C = (∑ i, z i) - ∑ i ∈ C, z i := by
  have he (i : ι) : (if i ∈ C then (0 : ℝ) else 1*z i) = z i - if i ∈ C then z i else 0 := by
    by_cases hi : i ∈ C <;> simp [hi]
  unfold keptSum
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  congr 1
  simp

theorem trimmedSum_is_min {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (r : ℕ) :
    trimmedSum z r = (cardinalityAttacks r).inf' (cardinalityAttacks_nonempty r)
      (keptSum (fun _ => 1) z) := by
  apply le_antisymm
  · apply Finset.le_inf' (cardinalityAttacks_nonempty r)
    intro C hC
    rw [keptSum_unit_eq]
    exact sub_le_sub_left (Finset.le_sup' (fun B => ∑ i ∈ B, z i) hC) _
  · obtain ⟨C,hC,he⟩ := Finset.exists_mem_eq_sup' (cardinalityAttacks_nonempty r)
      (fun C => ∑ i ∈ C, z i)
    have hh := Finset.inf'_le (keptSum (fun _ => 1) z) hC
    rw [keptSum_unit_eq] at hh
    change _ ≤ (∑ i, z i) - (cardinalityAttacks r).sup' (cardinalityAttacks_nonempty r)
      (fun C => ∑ i ∈ C, z i)
    rwa [he]

theorem trimmedSum_permutation {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (σ : Equiv.Perm ι) (r : ℕ) :
    trimmedSum (fun i => z (σ i)) r = trimmedSum z r := by
  simp only [trimmedSum,Equiv.sum_comp,largestSum_permutation]

end
end EvidenceFusion
