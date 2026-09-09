import Fusion.Disjoint
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max

namespace FusionDisjoint
open Finset
variable {G I Z : Type*} [Fintype G] [Fintype I] [DecidableEq G] [DecidableEq I]
  [AddCommGroup Z]

abbrev Selections (G I : Type*) := (G → Finset I) × (G → Finset I)

def GoodDifference (R : G → Finset I) (t : G → ℕ) (s : Selections G I) : Prop :=
  ∀ g, s.1 g ⊆ R g ∧ s.2 g ⊆ R g ∧ Disjoint (s.1 g) (s.2 g) ∧
    (s.1 g).card = (s.2 g).card ∧ (s.1 g).card ≤ t g

def GoodResidual (R : G → Finset I) (p : G → ℕ) (s : Selections G I) : Prop :=
  ∀ g, s.1 g ⊆ R g ∧ s.2 g ⊆ R g ∧ (s.1 g).card = p g ∧ (s.2 g).card = p g

def score (v : G → I → Z) (measure : Z → ℝ) (s : Selections G I) : ℝ :=
  measure (∑ g, ((∑ i ∈ s.1 g, v g i) - (∑ i ∈ s.2 g, v g i)))

noncomputable def candidates (P : Selections G I → Prop) : Finset (Selections G I) := by
  classical
  exact univ.filter P

theorem mem_candidates (P : Selections G I → Prop) (s : Selections G I) :
    s ∈ candidates P ↔ P s := by
  classical
  simp [candidates]

noncomputable def maximum {A : Type*} (S : Finset A) (f : A → ℝ) : ℝ := by
  classical
  exact if h : S.Nonempty then f (Classical.choose (exists_max_image S f h)) else 0

theorem maximum_witness {A : Type*} (S : Finset A) (f : A → ℝ) (h : S.Nonempty) :
    ∃ a ∈ S, maximum S f = f a ∧ ∀ b ∈ S, f b ≤ f a := by
  classical
  refine ⟨Classical.choose (exists_max_image S f h),?_,?_,?_⟩
  · exact (Classical.choose_spec (exists_max_image S f h)).1
  · simp [maximum,h]
  · exact (Classical.choose_spec (exists_max_image S f h)).2

theorem le_maximum {A : Type*} (S : Finset A) (f : A → ℝ) (a : A) (ha : a ∈ S) :
    f a ≤ maximum S f := by
  obtain ⟨b,hb,he,hmax⟩ := maximum_witness S f ⟨a,ha⟩
  rw [he]
  exact hmax a ha

theorem maximum_le {A : Type*} (S : Finset A) (f : A → ℝ) (h : S.Nonempty)
    (b : ℝ) (hb : ∀ a ∈ S, f a ≤ b) : maximum S f ≤ b := by
  obtain ⟨a,ha,he,_⟩ := maximum_witness S f h
  rw [he]
  exact hb a ha

theorem difference_nonempty (R : G → Finset I) (t : G → ℕ) :
    (candidates (GoodDifference R t)).Nonempty := by
  refine ⟨(fun _ => ∅,fun _ => ∅),(mem_candidates _ _).mpr ?_⟩
  intro g
  simp

theorem residual_nonempty (R : G → Finset I) (p : G → ℕ) (hp : ∀ g, p g ≤ (R g).card) :
    (candidates (GoodResidual R p)).Nonempty := by
  classical
  have hh (g : G) : ∃ A ⊆ R g, A.card = p g := exists_subset_card_eq (hp g)
  choose A ha hc using hh
  refine ⟨(A,A),(mem_candidates _ _).mpr ?_⟩
  intro g
  exact ⟨ha g,ha g,hc g,hc g⟩

noncomputable def potential (v : G → I → Z) (measure : Z → ℝ)
    (R : G → Finset I) (t : G → ℕ) : ℝ := maximum (candidates (GoodDifference R t)) (score v measure)
noncomputable def diameter (v : G → I → Z) (measure : Z → ℝ)
    (R : G → Finset I) (p : G → ℕ) : ℝ := maximum (candidates (GoodResidual R p)) (score v measure)

theorem residual_to_difference (v : G → I → Z) (measure : Z → ℝ)
    (R : G → Finset I) (p : G → ℕ) (hp : ∀ g, p g ≤ (R g).card)
    (s : Selections G I) (hs : GoodResidual R p s) :
    ∃ t : Selections G I, GoodDifference R (fun g => min (p g) ((R g).card-p g)) t ∧
      score v measure s = score v measure t := by
  classical
  have hh (g : G) : ∃ P Q : Finset I,
      (P ⊆ R g ∧ Q ⊆ R g ∧ Disjoint P Q ∧ P.card=Q.card ∧ P.card ≤ min (p g) ((R g).card-p g)) ∧
      (∑ i ∈ s.1 g, v g i)-(∑ i ∈ s.2 g, v g i) = (∑ i ∈ P, v g i)-(∑ i ∈ Q, v g i) := by
    have h := (Fusion.difference_set_identity (R g) (v g) (p g) (hp g) _).mp
      ⟨s.1 g,(hs g).1,s.2 g,(hs g).2.1,(hs g).2.2.1,(hs g).2.2.2,rfl⟩
    obtain ⟨P,hP,Q,hQ,hd,hc,hb,he⟩ := h
    exact ⟨P,Q,⟨hP,hQ,hd,hc,hb⟩,he⟩
  choose P Q hg he using hh
  refine ⟨(P,Q),hg,?_⟩
  unfold score
  congr 1
  apply sum_congr rfl
  intro g hg'
  exact he g

theorem difference_to_residual (v : G → I → Z) (measure : Z → ℝ)
    (R : G → Finset I) (p : G → ℕ) (hp : ∀ g, p g ≤ (R g).card)
    (s : Selections G I) (hs : GoodDifference R (fun g => min (p g) ((R g).card-p g)) s) :
    ∃ t : Selections G I, GoodResidual R p t ∧ score v measure s = score v measure t := by
  classical
  have hh (g : G) : ∃ A B : Finset I,
      (A ⊆ R g ∧ B ⊆ R g ∧ A.card=p g ∧ B.card=p g) ∧
      (∑ i ∈ s.1 g, v g i)-(∑ i ∈ s.2 g, v g i) = (∑ i ∈ A, v g i)-(∑ i ∈ B, v g i) := by
    have h := (Fusion.difference_set_identity (R g) (v g) (p g) (hp g) _).mpr
      ⟨s.1 g,(hs g).1,s.2 g,(hs g).2.1,(hs g).2.2.1,(hs g).2.2.2.1,(hs g).2.2.2.2,rfl⟩
    obtain ⟨A,hA,B,hB,ha,hb,he⟩ := h
    exact ⟨A,B,⟨hA,hB,ha,hb⟩,he⟩
  choose A B hg he using hh
  refine ⟨(A,B),hg,?_⟩
  unfold score
  congr 1
  apply sum_congr rfl
  intro g hg'
  exact he g

/-- Exact arbitrary-function diameter representation. Taking `measure` to
    be any norm yields the paper's vector completion diameter. -/
theorem diameter_eq_potential (v : G → I → Z) (measure : Z → ℝ)
    (R : G → Finset I) (p : G → ℕ) (hp : ∀ g, p g ≤ (R g).card) :
    diameter v measure R p = potential v measure R (fun g => min (p g) ((R g).card-p g)) := by
  apply le_antisymm
  · apply maximum_le _ _ (residual_nonempty R p hp)
    intro s hs
    obtain ⟨t,ht,he⟩ := residual_to_difference v measure R p hp s ((mem_candidates _ _).mp hs)
    rw [he]
    exact le_maximum _ _ t ((mem_candidates _ _).mpr ht)
  · apply maximum_le _ _ (difference_nonempty R _)
    intro s hs
    obtain ⟨t,ht,he⟩ := difference_to_residual v measure R p hp s ((mem_candidates _ _).mp hs)
    rw [he]
    exact le_maximum _ _ t ((mem_candidates _ _).mpr ht)

theorem potential_mono (v : G → I → Z) (measure : Z → ℝ)
    (R : G → Finset I) (s t : G → ℕ) (hst : ∀ g, s g ≤ t g) :
    potential v measure R s ≤ potential v measure R t := by
  apply maximum_le _ _ (difference_nonempty R s)
  intro x hx
  have hh := (mem_candidates _ _).mp hx
  apply le_maximum _ _ x
  apply (mem_candidates _ _).mpr
  intro g
  exact ⟨(hh g).1,(hh g).2.1,(hh g).2.2.1,(hh g).2.2.2.1,
    (hh g).2.2.2.2.trans (hst g)⟩

end FusionDisjoint
