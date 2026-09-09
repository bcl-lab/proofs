import Fusion.Basic
import Mathlib.Data.Finset.Card

namespace Fusion
open Finset

/-- Cancel common selected records without changing the target difference. -/
theorem cancel_common {ι : Type*} [DecidableEq ι] {V : Type*} [AddCommGroup V] (v : ι → V) (A B : Finset ι) :
    (∑ i ∈ A, v i) - (∑ i ∈ B, v i) =
    (∑ i ∈ A \ B, v i) - (∑ i ∈ B \ A, v i) := by
  exact (sum_sdiff_sub_sum_sdiff (s₁ := B) (s₂ := A) (f := v)).symm

/-- The two remainder sets in Equation S7 have equal size and the correct bound. -/
theorem remainders_card_bound {ι : Type*} [DecidableEq ι]
    (R A B : Finset ι) (k : ℕ) (hA : A ⊆ R) (hB : B ⊆ R)
    (hkA : A.card = k) (hkB : B.card = k) :
    (A \ B).card = (B \ A).card ∧
    (A \ B).card ≤ min k (R.card-k) := by
  have heq := card_sdiff_comm (hkA.trans hkB.symm)
  have hsmall := card_le_card (Finset.sdiff_subset : A \ B ⊆ A)
  have hR := card_le_card (union_subset hA hB)
  have hu := card_sdiff_add_card A B
  constructor
  · exact heq
  · apply Nat.le_min.mpr
    constructor <;> omega

/-- Pad two disjoint remainders by a common set, establishing the reverse
    combinatorial inclusion used in Equation S7. -/
theorem pad_remainders {ι : Type*} [DecidableEq ι]
    (R P Q : Finset ι) (k : ℕ) (hP : P ⊆ R) (hQ : Q ⊆ R)
    (hd : Disjoint P Q) (heq : P.card = Q.card)
    (hk : k ≤ R.card) (hh : P.card ≤ min k (R.card-k)) :
    ∃ C : Finset ι, C ⊆ R \ (P ∪ Q) ∧
      (P ∪ C).card = k ∧ (Q ∪ C).card = k := by
  have hU : P ∪ Q ⊆ R := union_subset hP hQ
  have hc := card_sdiff hU
  have huc := card_union_of_disjoint hd
  have h1 := (Nat.le_min.mp hh).1
  have h2 := (Nat.le_min.mp hh).2
  have hsize : k-P.card ≤ (R \ (P ∪ Q)).card := by omega
  obtain ⟨C,hC,hcc⟩ := exists_subset_card_eq hsize
  have hPC : Disjoint P C := by
    apply disjoint_left.mpr
    intro i hi hiC
    have hn := (mem_sdiff.mp (hC hiC)).2
    exact hn (mem_union_left Q hi)
  have hQC : Disjoint Q C := by
    apply disjoint_left.mpr
    intro i hi hiC
    have hn := (mem_sdiff.mp (hC hiC)).2
    exact hn (mem_union_right P hi)
  refine ⟨C,hC,?_,?_⟩
  · rw [card_union_of_disjoint hPC, hcc]; omega
  · rw [card_union_of_disjoint hQC, hcc]; omega

/-- General scalar Equation S7, stated as an equivalence of witnesses. -/
theorem difference_set_identity {ι : Type*} [DecidableEq ι]
    {V : Type*} [AddCommGroup V]
    (R : Finset ι) (v : ι → V) (k : ℕ) (hk : k ≤ R.card) (z : V) :
    (∃ A ⊆ R, ∃ B ⊆ R, A.card = k ∧ B.card = k ∧
      z = (∑ i ∈ A, v i)-(∑ i ∈ B, v i)) ↔
    (∃ P ⊆ R, ∃ Q ⊆ R, Disjoint P Q ∧ P.card = Q.card ∧
      P.card ≤ min k (R.card-k) ∧
      z = (∑ i ∈ P, v i)-(∑ i ∈ Q, v i)) := by
  constructor
  · rintro ⟨A,hA,B,hB,hkA,hkB,hz⟩
    have hb := remainders_card_bound R A B k hA hB hkA hkB
    refine ⟨A \ B, (Finset.sdiff_subset : A \ B ⊆ A).trans hA,
      B \ A, (Finset.sdiff_subset : B \ A ⊆ B).trans hB, ?_,hb.1,hb.2,?_⟩
    · apply disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
    · rw [hz, cancel_common]
  · rintro ⟨P,hP,Q,hQ,hd,heq,hh,hz⟩
    obtain ⟨C,hC,hPC,hQC⟩ := pad_remainders R P Q k hP hQ hd heq hk hh
    have hCR : C ⊆ R := hC.trans (Finset.sdiff_subset)
    have hdisjP : Disjoint P C := by
      apply disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp (hC hj)).2 (mem_union_left _ hi)
    have hdisjQ : Disjoint Q C := by
      apply disjoint_left.mpr
      intro i hi hj
      exact (mem_sdiff.mp (hC hj)).2 (mem_union_right _ hi)
    refine ⟨P ∪ C,union_subset hP hCR,Q ∪ C,union_subset hQ hCR,hPC,hQC,?_⟩
    rw [sum_union hdisjP, sum_union hdisjQ, hz]
    simp

/-- The arithmetic invariant behind the majority-answer adversary. -/
theorem majority_step (p q : ℕ) (h : 0 < p+q) :
    (if q ≤ p then min (p-1) q else min p (q-1)) =
      min (min p q) ((p+q-1)/2) := by
  split_ifs <;> omega

/-- Zero-coefficient slack counts represent an interval of possible totals. -/
theorem bounded_total_slack (L U m : ℕ) (hLU : L ≤ U) :
    (L ≤ m ∧ m ≤ U) ↔ ∃ s : ℕ, s ≤ U-L ∧ m+s = U := by
  constructor
  · intro h; exact ⟨U-m,by omega,by omega⟩
  · rintro ⟨s,hs,heq⟩; omega


def majorityProcess : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0,p,q => (p,q)
  | t+1,p,q => if q ≤ p then majorityProcess t (p-1) q else majorityProcess t p (q-1)

/-- Full majority-adversary invariant for every feasible number of reviews. -/
theorem majority_invariant (t p q : ℕ) (ht : t ≤ p+q) :
    (majorityProcess t p q).1 + (majorityProcess t p q).2 = p+q-t ∧
    min (majorityProcess t p q).1 (majorityProcess t p q).2 =
      min (min p q) ((p+q-t)/2) := by
  induction t generalizing p q with
  | zero =>
    change p+q = p+q ∧ min p q = min (min p q) ((p+q)/2)
    constructor
    · rfl
    · omega
  | succ t ih =>
    by_cases h : q ≤ p
    · have hp : 0 < p := by omega
      have hit : t ≤ p-1+q := by omega
      have hi := ih (p-1) q hit
      simp only [majorityProcess, if_pos h]
      constructor <;> omega
    · have hq : 0 < q := by omega
      have hit : t ≤ p+(q-1) := by omega
      have hi := ih p (q-1) hit
      simp only [majorityProcess, if_neg h]
      constructor <;> omega

/-- Integer rounding to the nearest multiple of five has an inclusive
    compatible-count interval of width four. -/
theorem round_five_compatibility (c : ℤ) :
    let r := 5*((c+2)/5)
    r-2 ≤ c ∧ c ≤ r+2 ∧ (r+2)-(r-2)=4 := by
  dsimp
  omega

end Fusion
