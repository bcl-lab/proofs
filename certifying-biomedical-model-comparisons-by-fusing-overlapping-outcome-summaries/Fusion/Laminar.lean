import Fusion.Basic
import Mathlib.Data.Finset.Max

namespace FusionLaminar
open Finset
variable {ι : Type*} [DecidableEq ι]

def Laminar (F : Finset (Finset ι)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, Disjoint A B ∨ A ⊆ B ∨ B ⊆ A

/-- Immediate strict inclusion, with sets themselves as node identifiers. -/
def Child (F : Finset (Finset ι)) (S C : Finset ι) : Prop :=
  C ∈ F ∧ C ⊂ S ∧ ∀ D ∈ F, C ⊂ D → D ⊆ S → D = S

theorem child_subset (F : Finset (Finset ι)) (S C : Finset ι)
    (h : Child F S C) : C ⊆ S := h.2.1.1

theorem child_smaller (F : Finset (Finset ι)) (S C : Finset ι)
    (h : Child F S C) : C.card < S.card := card_lt_card h.2.1

/-- Distinct immediate children in a laminar family are disjoint. -/
theorem children_disjoint (F : Finset (Finset ι)) (hl : Laminar F)
    (S A B : Finset ι) (hA : Child F S A) (hB : Child F S B) (hne : A ≠ B) :
    Disjoint A B := by
  rcases hl A hA.1 B hB.1 with hd | hab | hba
  · exact hd
  · have hs : A ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hab,hne⟩
    have he := hA.2.2 B hB.1 hs hB.2.1.1
    subst B
    exact False.elim (lt_irrefl _ (card_lt_card hB.2.1))
  · have hs : B ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨hba,hne.symm⟩
    have he := hB.2.2 A hA.1 hs hA.2.1.1
    subst A
    exact False.elim (lt_irrefl _ (card_lt_card hA.2.1))

/-- Singleton completion makes every element of a nonsingleton node belong
    to an immediate child. No tree-cover property is assumed. -/
theorem child_covers (F : Finset (Finset ι))
    (hsingle : ∀ i, {i} ∈ F) (S : Finset ι) (hsize : 1 < S.card)
    (i : ι) (hi : i ∈ S) : ∃ C, Child F S C ∧ i ∈ C := by
  classical
  let candidates := F.filter (fun C => C ⊂ S ∧ i ∈ C)
  have hproper : ({i} : Finset ι) ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨singleton_subset_iff.mpr hi,?_⟩
    intro he
    rw [← he,card_singleton] at hsize
    omega
  have hne : candidates.Nonempty := ⟨{i},mem_filter.mpr ⟨hsingle i,hproper,mem_singleton_self i⟩⟩
  obtain ⟨C,hC,hmax⟩ := exists_max_image candidates Finset.card hne
  have hc := mem_filter.mp hC
  refine ⟨C,⟨hc.1,hc.2.1,?_⟩,hc.2.2⟩
  intro D hD hCD hDS
  by_contra hn
  have hdproper : D ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hDS,hn⟩
  have hdi : i ∈ D := hCD.1 hc.2.2
  have hb := hmax D (mem_filter.mpr ⟨hD,hdproper,hdi⟩)
  have hc := card_lt_card hCD
  omega

/-- Every nonroot node has an immediate parent when the full set is present. -/
theorem parent_exists (F : Finset (Finset ι)) (U C : Finset ι)
    (hU : U ∈ F) (hC : C ∈ F) (hCU : C ⊂ U) : ∃ S ∈ F, Child F S C := by
  classical
  let candidates := F.filter (fun S => C ⊂ S)
  have hne : candidates.Nonempty := ⟨U,mem_filter.mpr ⟨hU,hCU⟩⟩
  obtain ⟨S,hS,hmin⟩ := exists_min_image candidates Finset.card hne
  have hs := mem_filter.mp hS
  refine ⟨S,hs.1,hC,hs.2,?_⟩
  intro D hD hCD hDS
  have hb := hmin D (mem_filter.mpr ⟨hD,hCD⟩)
  apply eq_of_subset_of_card_le hDS hb

theorem parent_unique (F : Finset (Finset ι)) (hl : Laminar F)
    (A B C : Finset ι) (hA : A ∈ F) (hB : B ∈ F) (hC : C.Nonempty)
    (hcA : Child F A C) (hcB : Child F B C) : A = B := by
  obtain ⟨i,hi⟩ := hC
  rcases hl A hA B hB with hd | hab | hba
  · exact False.elim (disjoint_left.mp hd (hcA.2.1.1 hi) (hcB.2.1.1 hi))
  · exact hcB.2.2 A hA hcA.2.1 hab
  · exact (hcA.2.2 B hB hcB.2.1 hba).symm

noncomputable def children (F : Finset (Finset ι)) (S : Finset ι) : Finset (Finset ι) := by
  classical
  exact F.filter (Child F S)

theorem mem_children (F : Finset (Finset ι)) (S C : Finset ι) :
    C ∈ children F S ↔ Child F S C := by
  classical
  simp only [children,mem_filter]
  exact ⟨fun h => h.2,fun h => ⟨h.1,h⟩⟩

/-- The inclusion-tree children really partition their parent node. -/
theorem children_union (F : Finset (Finset ι)) (hsingle : ∀ i, {i} ∈ F)
    (S : Finset ι) (hsize : 1 < S.card) : (children F S).biUnion id = S := by
  classical
  ext i
  simp only [mem_biUnion, id_eq]
  constructor
  · rintro ⟨C,hC,hi⟩
    exact (child_subset F S C ((mem_children F S C).mp hC)) hi
  · intro hi
    obtain ⟨C,hC,hiC⟩ := child_covers F hsingle S hsize i hi
    exact ⟨C,(mem_children F S C).mpr hC,hiC⟩

theorem sum_children {V : Type*} [AddCommMonoid V]
    (F : Finset (Finset ι)) (hl : Laminar F) (hsingle : ∀ i, {i} ∈ F)
    (S : Finset ι) (hsize : 1 < S.card) (w : ι → V) :
    (∑ C ∈ children F S, ∑ i ∈ C, w i) = ∑ i ∈ S, w i := by
  classical
  have hd : (children F S : Set (Finset ι)).Pairwise (fun A B => Disjoint (id A) (id B)) := by
    intro A hA B hB hne
    exact children_disjoint F hl S A B
      ((mem_children F S A).mp hA) ((mem_children F S B).mp hB) hne
  calc
    (∑ C ∈ children F S, ∑ i ∈ C, w i) = ∑ i ∈ (children F S).biUnion id, w i :=
      (sum_biUnion hd).symm
    _ = ∑ i ∈ S, w i := by rw [children_union F hsingle S hsize]

/-- Conservation and leaf values determine every tree arc flow, with the
    hierarchy derived from the laminar family rather than assumed. -/
theorem tree_flow_determined {V : Type*} [AddCommMonoid V]
    (F : Finset (Finset ι)) (hl : Laminar F) (hsingle : ∀ i, {i} ∈ F)
    (hne : ∀ S ∈ F, S.Nonempty) (w : ι → V) (flow : Finset ι → V)
    (hleaf : ∀ i, flow {i} = w i)
    (hcons : ∀ S ∈ F, 1 < S.card → flow S = ∑ C ∈ children F S, flow C) :
    ∀ S ∈ F, flow S = ∑ i ∈ S, w i := by
  classical
  intro S hS
  induction hn : S.card using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hs : S.card = 1
    · obtain ⟨i,hi⟩ := card_eq_one.mp hs
      rw [hi,hleaf,sum_singleton]
    · have hsize : 1 < S.card := by
        have hp := card_pos.mpr (hne S hS)
        omega
      rw [hcons S hS hsize,← sum_children F hl hsingle S hsize w]
      apply sum_congr rfl
      intro C hC
      have hc := (mem_children F S C).mp hC
      exact ih C.card (by have hh := child_smaller F S C hc; omega) C hc.1 rfl

/-- Count bounds on any laminar family are equivalent to bounds on the
    explicitly constructed inclusion-tree arcs. -/
theorem laminar_representation
    (F : Finset (Finset ι)) (hl : Laminar F) (hsingle : ∀ i, {i} ∈ F)
    (hne : ∀ S ∈ F, S.Nonempty) (w : ι → ℤ) (lower upper : Finset ι → ℤ) :
    (∀ S ∈ F, lower S ≤ (∑ i ∈ S, w i) ∧ (∑ i ∈ S, w i) ≤ upper S) ↔
    ∃ flow : Finset ι → ℤ,
      (∀ i, flow {i} = w i) ∧
      (∀ S ∈ F, 1 < S.card → flow S = ∑ C ∈ children F S, flow C) ∧
      (∀ S ∈ F, lower S ≤ flow S ∧ flow S ≤ upper S) := by
  constructor
  · intro h
    refine ⟨fun S => ∑ i ∈ S, w i,?_,?_,h⟩
    · intro i; exact sum_singleton _ _
    · intro S hS hs; exact (sum_children F hl hsingle S hs w).symm
  · rintro ⟨flow,hf,hc,hb⟩
    have he := tree_flow_determined F hl hsingle hne w flow hf hc
    intro S hS
    simpa only [he S hS] using hb S hS

end FusionLaminar
