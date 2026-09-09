import Fusion.NetworkOpt
import Fusion.LaminarComplete
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum

namespace FusionHierarchy
open Finset FusionLaminar FusionNetwork
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem has_parent (F : Finset (Finset ι)) (C : Finset ι)
    (hC : C ∈ completed F ∧ C ≠ univ) : ∃ S ∈ completed F, Child (completed F) S C := by
  exact parent_exists (completed F) univ C (completed_root F) hC.1
    (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hC.2⟩)

noncomputable def parent (F : Finset (Finset ι)) (C : Finset ι) : Option (Finset ι) := by
  classical
  exact if hC : C ∈ completed F ∧ C ≠ univ then some (Classical.choose (has_parent F C hC)) else none

theorem parent_root (F : Finset (Finset ι)) : parent F univ = none := by
  classical
  simp [parent]

theorem parent_outside (F : Finset (Finset ι)) (C : Finset ι) (h : C ∉ completed F) : parent F C = none := by
  classical
  simp [parent,h]

theorem parent_some_iff (F : Finset (Finset ι)) (hl : Laminar F) (S C : Finset ι) :
    parent F C = some S ↔ S ∈ completed F ∧ Child (completed F) S C := by
  classical
  constructor
  · intro hp
    unfold parent at hp
    split_ifs at hp with hc
    · have he := Option.some.inj hp
      have hs := Classical.choose_spec (has_parent F C hc)
      simpa only [he] using hs
  · rintro ⟨hS,hC⟩
    have hne : C ≠ univ := by
      intro he
      have hc := card_lt_card hC.2.1
      have hs := card_le_card (subset_univ S)
      rw [he] at hc
      omega
    have hc : C ∈ completed F ∧ C ≠ univ := ⟨hC.1,hne⟩
    have hp := Classical.choose_spec (has_parent F C hc)
    have he := parent_unique (completed F) (completed_laminar F hl)
      (Classical.choose (has_parent F C hc)) S C hp.1 hS
      (completed_nonempty F C hC.1) hp.2 hC
    simp [parent,hc,he]

noncomputable def treeOut (F : Finset (Finset ι)) (q : Finset ι → ℝ) (S : Finset ι) : ℝ := by
  classical
  exact ∑ C, if parent F C = some S then q C else 0

def leafTerm (y : ι → ℝ) (S : Finset ι) : ℝ := ∑ i, if {i}=S then y i else 0

theorem treeOut_children (F : Finset (Finset ι)) (hl : Laminar F)
    (q : Finset ι → ℝ) (S : Finset ι) (hS : S ∈ completed F) :
    treeOut F q S = ∑ C ∈ children (completed F) S, q C := by
  classical
  unfold treeOut
  rw [← sum_filter]
  congr 1
  ext C
  simp [parent_some_iff F hl,hS,mem_children]

theorem treeOut_outside (F : Finset (Finset ι)) (hl : Laminar F)
    (q : Finset ι → ℝ) (S : Finset ι) (hS : S ∉ completed F) : treeOut F q S = 0 := by
  classical
  simp [treeOut,parent_some_iff F hl,hS]

theorem treeOut_singleton (F : Finset (Finset ι)) (hl : Laminar F)
    (q : Finset ι → ℝ) (i : ι) : treeOut F q {i} = 0 := by
  classical
  apply sum_eq_zero
  intro C hC
  have hn : parent F C ≠ some {i} := by
    intro hp
    have hc := ((parent_some_iff F hl {i} C).mp hp).2
    have hs := card_lt_card hc.2.1
    have hn := card_pos.mpr (completed_nonempty F C hc.1)
    simp only [card_singleton] at hs
    omega
  simp only [if_neg hn]

theorem leafTerm_singleton (y : ι → ℝ) (i : ι) : leafTerm y {i} = y i := by
  simp [leafTerm]

theorem leafTerm_nonsingleton (y : ι → ℝ) (S : Finset ι) (hs : 1 < S.card) : leafTerm y S = 0 := by
  apply sum_eq_zero
  intro i hi
  have hn : ({i}:Finset ι) ≠ S := by intro he; rw [← he,card_singleton] at hs; omega
  simp [hn]

theorem leafTerm_outside (F : Finset (Finset ι)) (y : ι → ℝ) (S : Finset ι)
    (hS : S ∉ completed F) : leafTerm y S = 0 := by
  apply sum_eq_zero
  intro i hi
  have hn : ({i}:Finset ι) ≠ S := by intro he; exact hS (he ▸ completed_singleton F i)
  simp [hn]

noncomputable def treeLift (F : Finset (Finset ι)) (y : ι → ℝ) (S : Finset ι) : ℝ := by
  classical
  exact if S ∈ completed F then ∑ i ∈ S, y i else 0

theorem treeLift_node (F : Finset (Finset ι)) (hl : Laminar F) (y : ι → ℝ) (S : Finset ι) :
    treeOut F (treeLift F y) S + leafTerm y S = treeLift F y S := by
  classical
  by_cases hS : S ∈ completed F
  · by_cases hs : S.card = 1
    · obtain ⟨i,rfl⟩ := card_eq_one.mp hs
      rw [treeOut_singleton F hl,leafTerm_singleton]
      simp [treeLift,completed_singleton]
    · have hsize : 1 < S.card := by
        have hp := card_pos.mpr (completed_nonempty F S hS)
        omega
      rw [treeOut_children F hl _ S hS,leafTerm_nonsingleton y S hsize,add_zero]
      have hc : (∑ C ∈ children (completed F) S, treeLift F y C) =
          ∑ C ∈ children (completed F) S, ∑ i ∈ C, y i := by
        apply sum_congr rfl
        intro C hC
        simp [treeLift,((mem_children _ _ _).mp hC).1]
      rw [hc,sum_children (completed F) (completed_laminar F hl) (completed_singleton F) S hsize]
      simp [treeLift,hS]
  · rw [treeOut_outside F hl _ S hS,leafTerm_outside F y S hS]
    simp [treeLift,hS]

theorem node_determines_tree (F : Finset (Finset ι)) (hl : Laminar F)
    (q : Finset ι → ℝ) (y : ι → ℝ)
    (hc : ∀ S, treeOut F q S + leafTerm y S = q S) :
    ∀ S ∈ completed F, q S = ∑ i ∈ S, y i := by
  apply tree_flow_determined (completed F) (completed_laminar F hl)
    (completed_singleton F) (completed_nonempty F) y q
  · intro i
    have hh := hc {i}
    rw [treeOut_singleton F hl,leafTerm_singleton,zero_add] at hh
    exact hh.symm
  · intro S hS hs
    have hh := hc S
    rw [treeOut_children F hl q S hS,leafTerm_nonsingleton y S hs,add_zero] at hh
    exact hh.symm

noncomputable def rootOut (F : Finset (Finset ι)) (q : Finset ι → ℝ) : ℝ := by
  classical
  exact ∑ C, if parent F C = none then q C else 0

theorem rootOut_eq (F : Finset (Finset ι)) (q : Finset ι → ℝ)
    (hz : ∀ S, S ∉ completed F → q S = 0) : rootOut F q = q univ := by
  classical
  unfold rootOut
  rw [sum_eq_single univ]
  · simp [parent_root]
  · intro C hC hne
    by_cases hc : C ∈ completed F
    · simp [parent,hc,hne]
    · simp [hz C hc]
  · simp

end FusionHierarchy
