import Fusion.Laminar
import Fusion.Flow

namespace FusionLaminar
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Add the full set and every singleton, and remove empty original nodes. -/
noncomputable def completed (F : Finset (Finset ι)) : Finset (Finset ι) :=
  insert univ ((F.filter Finset.Nonempty) ∪ (univ.image fun i : ι => {i}))

theorem completed_root (F : Finset (Finset ι)) : univ ∈ completed F := by
  classical
  exact mem_insert_self _ _

theorem completed_singleton (F : Finset (Finset ι)) (i : ι) : {i} ∈ completed F := by
  classical
  simp [completed]

theorem completed_original (F : Finset (Finset ι)) (S : Finset ι)
    (h : S ∈ F) (hs : S.Nonempty) : S ∈ completed F := by
  classical
  simp only [completed,mem_insert,mem_union,mem_filter]
  exact Or.inr (Or.inl ⟨h,hs⟩)

theorem completed_nonempty (F : Finset (Finset ι)) :
    ∀ S ∈ completed F, S.Nonempty := by
  classical
  intro S h
  simp only [completed,mem_insert,mem_union,mem_filter,mem_image] at h
  rcases h with rfl | ⟨_,hs⟩ | ⟨i,_,rfl⟩
  · exact univ_nonempty
  · exact hs
  · exact singleton_nonempty _

theorem singleton_laminar (i : ι) (S : Finset ι) :
    Disjoint {i} S ∨ {i} ⊆ S ∨ S ⊆ {i} := by
  by_cases h : i ∈ S
  · exact Or.inr (Or.inl (singleton_subset_iff.mpr h))
  · exact Or.inl (disjoint_singleton_left.mpr h)

theorem completed_laminar (F : Finset (Finset ι)) (hl : Laminar F) :
    Laminar (completed F) := by
  classical
  intro A hA B hB
  simp only [completed,mem_insert,mem_union,mem_filter,mem_image] at hA hB
  rcases hA with rfl | ⟨ha,_⟩ | ⟨i,_,rfl⟩
  · exact Or.inr (Or.inr (subset_univ _))
  · rcases hB with rfl | ⟨hb,_⟩ | ⟨j,_,rfl⟩
    · exact Or.inr (Or.inl (subset_univ _))
    · exact hl A ha B hb
    · rcases singleton_laminar j A with hd | hs | hs
      · exact Or.inl hd.symm
      · exact Or.inr (Or.inr hs)
      · exact Or.inr (Or.inl hs)
  · exact singleton_laminar i B

/-- Conservation for the actual completed hierarchy, with original count
    bounds retained even when the original family contains the empty set. -/
def TreeWitness (F : Finset (Finset ι)) (y : ι → ℤ)
    (lower upper : Finset ι → ℤ) (flow : Finset ι → ℤ) : Prop :=
  flow ∅ = 0 ∧
  (∀ i, flow {i} = y i) ∧
  (∀ S ∈ completed F, 1 < S.card → flow S = ∑ C ∈ children (completed F) S, flow C) ∧
  (∀ S ∈ F, lower S ≤ flow S ∧ flow S ≤ upper S)

theorem completed_representation (F : Finset (Finset ι)) (hl : Laminar F)
    (y : ι → ℤ) (lower upper : Finset ι → ℤ) :
    (∀ S ∈ F, lower S ≤ (∑ i ∈ S, y i) ∧ (∑ i ∈ S, y i) ≤ upper S) ↔
      ∃ flow, TreeWitness F y lower upper flow := by
  constructor
  · intro h
    refine ⟨fun S => ∑ i ∈ S, y i,?_,?_,?_,h⟩
    · exact sum_empty
    · intro i; exact sum_singleton _ _
    · intro S hS hs
      exact (sum_children (completed F) (completed_laminar F hl)
        (completed_singleton F) S hs y).symm
  · rintro ⟨flow,he,hf,hc,hb⟩
    have hd := tree_flow_determined (completed F) (completed_laminar F hl)
      (completed_singleton F) (completed_nonempty F) y flow hf hc
    intro S hS
    by_cases hn : S.Nonempty
    · simpa only [hd S (completed_original F S hS hn)] using hb S hS
    · have hs : S = ∅ := not_nonempty_iff_eq_empty.mp hn
      subst S
      simpa only [he,sum_empty] using hb ∅ hS

/-- The source or sink arc carries the global total, derived from conservation. -/
theorem root_flow_total (F : Finset (Finset ι)) (hl : Laminar F)
    (y : ι → ℤ) (lower upper : Finset ι → ℤ) (flow : Finset ι → ℤ)
    (h : TreeWitness F y lower upper flow) : flow univ = ∑ i, y i := by
  exact tree_flow_determined (completed F) (completed_laminar F hl)
    (completed_singleton F) (completed_nonempty F) y flow h.2.1 h.2.2.1
    univ (completed_root F)

/-- Integer correspondence for both derived inclusion trees joined through
    their common unit-capacity record variables. -/
theorem two_completed_trees (A B : Finset (Finset ι))
    (ha : Laminar A) (hb : Laminar B) (la ua lb ub : Finset ι → ℤ)
    (M : ℤ) (O : Finset ι) (observed y : ι → ℤ) :
    ((∀ i, y i = 0 ∨ y i = 1) ∧ (∑ i, y i) = M ∧
      (∀ i ∈ O, y i = observed i) ∧
      (∀ S ∈ A, la S ≤ (∑ i ∈ S, y i) ∧ (∑ i ∈ S, y i) ≤ ua S) ∧
      (∀ S ∈ B, lb S ≤ (∑ i ∈ S, y i) ∧ (∑ i ∈ S, y i) ≤ ub S)) ↔
    ((∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (∀ i ∈ O, y i = observed i) ∧
      ∃ fA fB, TreeWitness A y la ua fA ∧ TreeWitness B y lb ub fB ∧
        fA univ = M ∧ fB univ = M) := by
  constructor
  · rintro ⟨hy,hM,hO,hA,hB⟩
    obtain ⟨fA,hfA⟩ := (completed_representation A ha y la ua).mp hA
    obtain ⟨fB,hfB⟩ := (completed_representation B hb y lb ub).mp hB
    refine ⟨fun i => (Fusion.integer_unit_capacity _).mpr (hy i),hO,fA,fB,hfA,hfB,?_,?_⟩
    · exact (root_flow_total A ha y la ua fA hfA).trans hM
    · exact (root_flow_total B hb y lb ub fB hfB).trans hM
  · rintro ⟨hy,hO,fA,fB,hA,hB,hM,_⟩
    exact ⟨fun i => (Fusion.integer_unit_capacity _).mp (hy i),
      (root_flow_total A ha y la ua fA hA).symm.trans hM,hO,
      (completed_representation A ha y la ua).mpr ⟨fA,hA⟩,
      (completed_representation B hb y lb ub).mpr ⟨fB,hB⟩⟩

end FusionLaminar
