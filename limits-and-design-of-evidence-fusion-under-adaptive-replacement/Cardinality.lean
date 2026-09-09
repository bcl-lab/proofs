import ModelBridge

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def cardinalityAttacks (k : ℕ) : Finset (Finset ι) :=
  univ.filter (fun C => C.card ≤ k)

theorem mem_cardinalityAttacks (k : ℕ) (C : Finset ι) :
    C ∈ cardinalityAttacks k ↔ C.card ≤ k := by simp [cardinalityAttacks]

theorem cardinalityAttacks_nonempty (k : ℕ) : (cardinalityAttacks (ι := ι) k).Nonempty :=
  ⟨∅,by simp [cardinalityAttacks]⟩

theorem cardinalityAttacks_downward (k : ℕ) :
    DownwardClosed (cardinalityAttacks (ι := ι) k) := by
  intro C hC B hBC
  exact (mem_cardinalityAttacks k B).mpr
    ((Finset.card_le_card hBC).trans ((mem_cardinalityAttacks k C).mp hC))

theorem compatible_cardinality (k : ℕ) (x y : ι → ℝ) :
    Compatible (cardinalityAttacks k) x y ↔
      (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧ hamming x y ≤ k := by
  rw [compatible_iff_differences _ (cardinalityAttacks_downward k)]
  simp [cardinalityAttacks,hamming]

theorem projected_cardinality (k : ℕ) (w : ι → ℝ) (B : Finset ι) :
    B ∈ projectedAttacks (cardinalityAttacks k) w ↔
      B ⊆ positiveSupport w ∧ B.card ≤ k := by
  constructor
  · intro hB
    exact ⟨projected_subset_support _ w hB,
      (mem_cardinalityAttacks k B).mp
        (projected_is_allowed _ w (cardinalityAttacks_downward k) hB)⟩
  · rintro ⟨hBs,hBk⟩
    apply Finset.mem_image.mpr
    exact ⟨B,(mem_cardinalityAttacks k B).mpr hBk,Finset.inter_eq_left.mpr hBs⟩

theorem cardinality_empty_intersection_iff (k : ℕ) (w : ι → ℝ) :
    EmptyMaximalIntersection (cardinalityAttacks k) w ↔
      positiveSupport w = ∅ ∨ k < (positiveSupport w).card := by
  constructor
  · intro he
    by_cases hk : k < (positiveSupport w).card
    · exact Or.inr hk
    · left
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro i hi
      obtain ⟨B,hB,hiB⟩ := he i
      have hI : positiveSupport w ∈ projectedAttacks (cardinalityAttacks k) w :=
        (projected_cardinality k w _).mpr ⟨Finset.Subset.refl _,Nat.le_of_not_gt hk⟩
      exact hiB (hB.2 _ hI (projected_subset_support _ w hB.1) hi)
  · intro hs i
    rcases hs with hz | hk
    · refine ⟨∅,⟨(projected_cardinality k w _).mpr ⟨by simp,by simp⟩,?_⟩,by simp⟩
      intro D hD _
      simpa [hz] using (projected_cardinality k w D).mp hD |>.1
    · by_cases hi : i ∈ positiveSupport w
      · have herase : k ≤ ((positiveSupport w).erase i).card := by
          rw [Finset.card_erase_of_mem hi]
          omega
        obtain ⟨B,hBs,hBk⟩ := Finset.exists_subset_card_eq herase
        have hBsup : B ⊆ positiveSupport w := hBs.trans (Finset.erase_subset _ _)
        refine ⟨B,⟨(projected_cardinality k w B).mpr ⟨hBsup,hBk.le⟩,?_⟩,?_⟩
        · intro D hD hBD
          have hDk := ((projected_cardinality k w D).mp hD).2
          have heq : B = D := Finset.eq_of_subset_of_card_le hBD (by omega)
          exact heq.symm ▸ Finset.Subset.refl B
        · intro hiB
          exact Finset.not_mem_erase i _ (hBs hiB)
      · have hzero : (∅ : Finset ι) ∈ projectedAttacks (cardinalityAttacks k) w :=
          (projected_cardinality k w _).mpr ⟨by simp,by simp⟩
        obtain ⟨B,hB,_⟩ := maximal_projected_extension _ w hzero
        exact ⟨B,hB,fun hiB => hi (projected_subset_support _ w hB.1 hiB)⟩

theorem cardinality_admissibility (k : ℕ) (a : ℝ) (w : ι → ℝ)
    (ha : 0 ≤ a) (hw : ∀ i, 0 ≤ w i) (hn : a + ∑ i, w i = 1) :
    ProbabilityAdmissible (cardinalityAttacks k)
      (fun y => robustAffine a w y (cardinalityAttacks k) (cardinalityAttacks_nonempty k)) ↔
      positiveSupport w = ∅ ∨ k < (positiveSupport w).card := by
  rw [exact_probability_admissibility _ _ (cardinalityAttacks_downward k) a w ha hw hn]
  exact cardinality_empty_intersection_iff k w

end
end EvidenceFusion
