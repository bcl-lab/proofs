import OrderStatistics

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

def zeroExtend {n : ℕ} (v : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then v ⟨i,h⟩ else 0

def layerDifferences {n : ℕ} (v : Fin n → ℝ) (j : Fin n) : ℝ :=
  zeroExtend v j-zeroExtend v (j+1)

theorem layerDifferences_nonneg {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hs : Antitone v) (j : Fin n) : 0 ≤ layerDifferences v j := by
  unfold layerDifferences zeroExtend
  simp only [j.isLt,dif_pos]
  split_ifs with hj
  · exact sub_nonneg.mpr (hs (show j ≤ ⟨j+1,hj⟩ from Nat.le_succ _))
  · simpa using hv j

theorem layers_reconstruct {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (∑ j, if i ≤ j then layerDifferences v j else 0) = v i := by
  let d : ℕ → ℝ := fun j => zeroExtend v j-zeroExtend v (j+1)
  have he := Fin.sum_univ_eq_sum_range (fun j => if (i : ℕ) ≤ j then d j else 0) n
  change (∑ j : Fin n, if (i : ℕ) ≤ (j : ℕ) then d j else 0) = v i
  rw [he,← Finset.sum_filter]
  rw [← Finset.sum_range_sub_sum_range (f := d) i.isLt.le]
  dsimp [d]
  rw [Finset.sum_range_sub',Finset.sum_range_sub']
  simp [zeroExtend,i.isLt]

def tailIndices (n r : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => r ≤ (i : ℕ))

theorem trimmedSum_sorted_tail {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hs : Antitone v) (r : ℕ) : trimmedSum v r = ∑ i ∈ tailIndices n r, v i := by
  rw [trimmedSum,largestSum_sorted v hv hs r]
  have he : (∑ i, v i) = (∑ i ∈ headIndices n r, v i) + ∑ i ∈ tailIndices n r, v i := by
    rw [headIndices,tailIndices,Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : (i : ℕ) < r
    · simp [hi,Nat.not_le.mpr hi]
    · simp [hi,Nat.le_of_not_gt hi]
  linarith

theorem tail_prefix_count {n : ℕ} (r : ℕ) (j : Fin n) :
    ((tailIndices n r).filter (fun i => i ≤ j)).card = (j : ℕ)+1-r := by
  by_cases hr : r < n
  · have he : (tailIndices n r).filter (fun i => i ≤ j) = Finset.Icc (⟨r,hr⟩ : Fin n) j := by
      ext i
      simp only [tailIndices,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Icc]
      rfl
    simp [he]
  · have he : tailIndices n r = ∅ := by
      ext i
      simp [tailIndices,show ¬ r ≤ (i : ℕ) from by omega]
    simp [he,show (j : ℕ)+1-r = 0 from by omega]

def prefixReciprocal {n : ℕ} (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ i, if i ≤ j then 1/x i else 0

theorem prefixReciprocal_pos {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (j : Fin n) :
    0 < prefixReciprocal x j := by
  have hh : 1/x j ≤ prefixReciprocal x j := by
    have h := Finset.single_le_sum
      (fun i (_ : i ∈ Finset.univ) => show 0 ≤ (if i ≤ j then 1/x i else 0) by
        split_ifs; exact (one_div_pos.mpr (hx i)).le; exact le_rfl) (Finset.mem_univ j)
    simpa [prefixReciprocal] using h
  exact (one_div_pos.mpr (hx j)).trans_le hh

def positiveCapacity {n : ℕ} [NeZero n] (x : Fin n → ℝ) (r : ℕ) : ℝ :=
  layerOptimum (prefixReciprocal x) (fun j => ((j : ℕ)+1-r : ℕ))

theorem sorted_contribution_capacity {n : ℕ} [NeZero n] (x v : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hv : ∀ i, 0 ≤ v i) (hs : Antitone v)
    (hbudget : ∑ i, v i/x i ≤ 1) (r : ℕ) :
    trimmedSum v r ≤ positiveCapacity x r := by
  have hbudget' : ∑ j, layerDifferences v j*prefixReciprocal x j ≤ 1 := by
    have he := layer_cost_identity (layerDifferences v) (fun i => 1/x i)
    simp_rw [layers_reconstruct] at he
    simp only [prefixReciprocal] at *
    rw [← he]
    simpa only [mul_one_div] using hbudget
  have ht := layer_tail_identity (layerDifferences v) (tailIndices n r)
  simp_rw [layers_reconstruct,tail_prefix_count] at ht
  rw [trimmedSum_sorted_tail v hv hs r,ht]
  exact (sharp_layer_program (prefixReciprocal x) (fun j => (((j : ℕ)+1-r : ℕ) : ℝ))
    (prefixReciprocal_pos x hx) (fun _ => Nat.cast_nonneg _)).1 _
    (layerDifferences_nonneg v hv hs) hbudget'

/-- The complete upper bound for arbitrary nonnegative contributions on a
positive, decreasing clean vector. The contribution sorting is proved here. -/
theorem positive_capacity_upper {n : ℕ} [NeZero n] (x v : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hsx : Antitone x) (hv : ∀ i, 0 ≤ v i)
    (hbudget : ∑ i, v i/x i ≤ 1) (r : ℕ) :
    trimmedSum v r ≤ positiveCapacity x r := by
  let σ := descendingPermutation v
  let u := fun i => v (σ i)
  have hu : Antitone u := descendingPermutation_antitone v
  have hc : Monotone (fun i => 1/x i) := by
    intro i j hij
    exact one_div_le_one_div_of_le (hx j) (hsx hij)
  have hcost := rearranged_cost_le u (fun i => 1/x i) σ.symm (hu.antivary hc)
  have hb : ∑ i, u i/x i ≤ 1 := by
    simp only [u,Equiv.apply_symm_apply,mul_one_div] at hcost
    exact hcost.trans hbudget
  have hh := sorted_contribution_capacity x u hx (fun i => hv _) hu hb r
  simpa only [u,trimmedSum_permutation] using hh

theorem positive_capacity_attained {n : ℕ} [NeZero n] (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (r : ℕ) :
    ∃ v : Fin n → ℝ, (∀ i, 0 ≤ v i) ∧ (∑ i, v i/x i = 1) ∧
      trimmedSum v r = positiveCapacity x r := by
  obtain ⟨d,hd,hcost,hvalue⟩ :=
    (sharp_layer_program (prefixReciprocal x) (fun j => (((j : ℕ)+1-r : ℕ) : ℝ))
      (prefixReciprocal_pos x hx) (fun _ => Nat.cast_nonneg _)).2
  let v := fun i => ∑ j, if i ≤ j then d j else 0
  have hv (i : Fin n) : 0 ≤ v i := Finset.sum_nonneg (fun j _ => by
    split_ifs; exact hd j; exact le_rfl)
  have hs : Antitone v := by
    intro i j hij
    apply Finset.sum_le_sum
    intro l _
    by_cases hjl : j ≤ l
    · simp [hjl,hij.trans hjl]
    · by_cases hil : i ≤ l
      · simp [hjl,hil,hd l]
      · simp [hjl,hil]
  refine ⟨v,hv,?_,?_⟩
  · have he := layer_cost_identity d (fun i => 1/x i)
    change (∑ i, (∑ j, if i ≤ j then d j else 0)/x i) = 1
    simp only [mul_one_div] at he
    exact he.trans hcost
  · rw [trimmedSum_sorted_tail v hv hs r]
    have he := layer_tail_identity d (tailIndices n r)
    simp_rw [tail_prefix_count] at he
    exact he.trans hvalue

end
end EvidenceFusion
