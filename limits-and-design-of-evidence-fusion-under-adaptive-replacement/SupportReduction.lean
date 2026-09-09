import PositiveCapacity

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem sum_on_embedding (e : κ ↪ ι) (z : ι → ℝ)
    (hz : ∀ i, (¬ ∃ j, e j = i) → z i = 0) :
    (∑ i, z i) = ∑ j, z (e j) := by
  have he : (∑ i ∈ Finset.univ.map e, z i) = ∑ i, z i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    apply hz i
    simpa using hi
  simpa only [Finset.sum_map] using he.symm

theorem embedding_preimage_card_le (e : κ ↪ ι) (C : Finset ι) :
    (Finset.univ.filter (fun j => e j ∈ C)).card ≤ C.card := by
  let D := Finset.univ.filter (fun j => e j ∈ C)
  have hs : D.map e ⊆ C := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact (Finset.mem_filter.mp hj).2
  have hh := Finset.card_le_card hs
  simpa only [Finset.card_map] using hh

theorem largestSum_restrict_support (e : κ ↪ ι) (z : ι → ℝ)
    (hz : ∀ i, (¬ ∃ j, e j = i) → z i = 0) (r : ℕ) :
    largestSum z r = largestSum (fun j => z (e j)) r := by
  apply le_antisymm
  · apply Finset.sup'_le (cardinalityAttacks_nonempty r)
    intro C hC
    let D := Finset.univ.filter (fun j => e j ∈ C)
    have hD : D ∈ cardinalityAttacks r := (mem_cardinalityAttacks r D).mpr
      ((embedding_preimage_card_le e C).trans ((mem_cardinalityAttacks r C).mp hC))
    have he := sum_on_embedding e (fun i => if i ∈ C then z i else 0) (by
      intro i hi; simp [hz i hi])
    have he' : (∑ i ∈ C, z i) = ∑ j ∈ D, z (e j) := by
      simpa [Finset.sum_filter,D] using he
    rw [he']
    exact Finset.le_sup' (fun B => ∑ j ∈ B, z (e j)) hD
  · apply Finset.sup'_le (cardinalityAttacks_nonempty r)
    intro C hC
    have hD : C.map e ∈ cardinalityAttacks r := by
      rw [mem_cardinalityAttacks,Finset.card_map]
      exact (mem_cardinalityAttacks r C).mp hC
    have hh := Finset.le_sup' (fun B => ∑ j ∈ B, z j) hD
    simpa only [Finset.sum_map] using hh

theorem trimmedSum_restrict_support (e : κ ↪ ι) (z : ι → ℝ)
    (hz : ∀ i, (¬ ∃ j, e j = i) → z i = 0) (r : ℕ) :
    trimmedSum z r = trimmedSum (fun j => z (e j)) r := by
  simp only [trimmedSum,sum_on_embedding e z hz,largestSum_restrict_support e z hz]

theorem positiveCapacity_nonneg {n : ℕ} [NeZero n] (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (r : ℕ) : 0 ≤ positiveCapacity x r := by
  obtain ⟨j,hj⟩ := (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
  apply (div_nonneg (Nat.cast_nonneg _) (prefixReciprocal_pos x hx j).le).trans
  exact Finset.le_sup' (fun j : Fin n => (((j : ℕ)+1-r : ℕ) : ℝ)/prefixReciprocal x j) hj

theorem sorted_capacity_homogeneous {n : ℕ} [NeZero n] (x v : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hv : ∀ i, 0 ≤ v i) (hs : Antitone v) (r : ℕ) :
    trimmedSum v r ≤ positiveCapacity x r * (∑ i, v i/x i) := by
  have heCost := layer_cost_identity (layerDifferences v) (fun i => 1/x i)
  simp_rw [layers_reconstruct] at heCost
  simp only [mul_one_div] at heCost
  have heTail := layer_tail_identity (layerDifferences v) (tailIndices n r)
  simp_rw [layers_reconstruct,tail_prefix_count] at heTail
  rw [trimmedSum_sorted_tail v hv hs r,heTail,heCost,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hh := Finset.le_sup' (fun j : Fin n => (((j : ℕ)+1-r : ℕ) : ℝ)/prefixReciprocal x j)
    (Finset.mem_univ j)
  change (((j : ℕ)+1-r : ℕ) : ℝ)/prefixReciprocal x j ≤ positiveCapacity x r at hh
  have hb := (div_le_iff₀ (prefixReciprocal_pos x hx j)).mp hh
  have hm := mul_le_mul_of_nonneg_left hb (layerDifferences_nonneg v hv hs j)
  dsimp [prefixReciprocal] at *
  nlinarith

theorem positive_capacity_homogeneous {n : ℕ} [NeZero n] (x v : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hsx : Antitone x) (hv : ∀ i, 0 ≤ v i) (r : ℕ) :
    trimmedSum v r ≤ positiveCapacity x r * (∑ i, v i/x i) := by
  let σ := descendingPermutation v
  let u := fun i => v (σ i)
  have hu : Antitone u := descendingPermutation_antitone v
  have hc : Monotone (fun i => 1/x i) := by
    intro i j hij
    exact one_div_le_one_div_of_le (hx j) (hsx hij)
  have hcost := rearranged_cost_le u (fun i => 1/x i) σ.symm (hu.antivary hc)
  simp only [u,Equiv.apply_symm_apply,mul_one_div] at hcost
  have hh := sorted_capacity_homogeneous x u hx (fun i => hv _) hu r
  have hm := mul_le_mul_of_nonneg_left hcost (positiveCapacity_nonneg x hx r)
  simpa only [u,trimmedSum_permutation] using hh.trans hm

/-- Upper bound after deleting zero-valued coordinates. The embedding lists
the positive coordinates in decreasing order. -/
theorem nonnegative_capacity_upper {p : ℕ} [NeZero p] (e : Fin p ↪ ι) (x w : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hw : ∀ i, 0 ≤ w i)
    (hpos : ∀ j, 0 < x (e j)) (hsort : Antitone (fun j => x (e j)))
    (hzero : ∀ i, (¬ ∃ j, e j = i) → x i = 0) (r : ℕ) :
    trimmedSum (fun i => w i*x i) r ≤
      positiveCapacity (fun j => x (e j)) r * ∑ i, w i := by
  rw [trimmedSum_restrict_support e _ (fun i hi => by simp [hzero i hi])]
  have hh := positive_capacity_homogeneous (fun j => x (e j)) (fun j => w (e j)*x (e j))
    hpos hsort (fun j => mul_nonneg (hw _) (hx _)) r
  have he (j : Fin p) : w (e j)*x (e j)/x (e j) = w (e j) := mul_div_cancel_right₀ _ (hpos j).ne'
  simp_rw [he] at hh
  have hs : (∑ j, w (e j)) ≤ ∑ i, w i := by
    have hh := Finset.sum_le_univ_sum_of_nonneg (s := Finset.univ.map e) hw
    simpa only [Finset.sum_map] using hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (positiveCapacity_nonneg _ hpos r))

end
end EvidenceFusion
