import Fusion.DisjointMinimax
import Fusion.DisjointSemantics

namespace FusionDisjoint
open Finset
variable {G I Z : Type*} [Fintype G] [Fintype I] [DecidableEq G] [DecidableEq I]
  [AddCommGroup Z]

def initialConfig (R : G → Finset I) (m : G → ℕ) : Config G I :=
  ⟨R,m,fun g => (R g).card-m g,fun _ => ∅⟩

theorem initial_good (R : G → Finset I) (m : G → ℕ) (hm : ∀ g,m g ≤ (R g).card) :
    Good (initialConfig R m) := by
  intro g
  dsimp [initialConfig]
  have h := hm g
  omega

def remainingOf (R : G → Finset I) (S : Finset (G × I)) (g : G) : Finset I :=
  (R g).filter (fun i => (g,i) ∉ S)

noncomputable def reviewedOf (R T : G → Finset I) : Finset (G × I) :=
  univ.filter (fun q => q.2 ∈ R q.1 ∧ q.2 ∉ T q.1)

theorem remaining_subset (R : G → Finset I) (S : Finset (G × I)) (g : G) :
    remainingOf R S g ⊆ R g := filter_subset _ _

theorem reviewed_remaining (R : G → Finset I) (S : Finset (G × I))
    (hS : ∀ q ∈ S,q.2 ∈ R q.1) : reviewedOf R (remainingOf R S) = S := by
  ext q
  simp only [reviewedOf,mem_filter,mem_univ,true_and,remainingOf]
  by_cases hq : q ∈ S
  · simp [hq,hS q hq]
  · simp [hq]

theorem remaining_reviewed (R T : G → Finset I) (hT : ∀ g,T g ⊆ R g) :
    remainingOf R (reviewedOf R T) = T := by
  funext g
  ext i
  simp only [remainingOf,mem_filter,reviewedOf,mem_univ,true_and]
  by_cases hi : i ∈ T g
  · simp [hi,hT g hi]
  · simp [hi]

theorem fixedQueries_exact_set (R : G → Finset I) (S : Finset (G × I))
    (hS : ∀ q ∈ S,q.2 ∈ R q.1) :
    (fixedQueries R (remainingOf R S)).toFinset = S := by
  simpa only [fixedQueries,toList_toFinset] using reviewed_remaining R S hS

def AllowedRemaining (R : G → Finset I) (F : Finset (Finset (G × I))) : Finset (G → Finset I) :=
  F.image (remainingOf R)

theorem allowed_nonempty (R : G → Finset I) (F : Finset (Finset (G × I))) (hF : F.Nonempty) :
    (AllowedRemaining R F).Nonempty := hF.image _

theorem allowed_subset (R : G → Finset I) (F : Finset (Finset (G × I))) :
    ∀ T ∈ AllowedRemaining R F,∀ g,T g ⊆ R g := by
  intro T hT
  obtain ⟨S,_,rfl⟩ := mem_image.mp hT
  exact remaining_subset R S

theorem fixed_prefixes_permitted (R : G → Finset I) (F : Finset (Finset (G × I)))
    (hdown : ∀ S ∈ F,∀ T ⊆ S,T ∈ F) (S : Finset (G × I)) (hS : S ∈ F)
    (hactual : ∀ q ∈ S,q.2 ∈ R q.1) (j : ℕ) :
    ((fixedQueries R (remainingOf R S)).take j).toFinset ∈ F := by
  apply hdown S hS
  intro q hq
  rw [← fixedQueries_exact_set R S hactual]
  exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hq))

set_option maxHeartbeats 1000000 in
/-- Equation S8 in the paper's original review-set notation, with a
    nonempty family of allowed sets. Groups are tagged, hence disjoint.
    The displayed threshold is min(m_g,n_g-m_g,floor(|R_g|/2)). -/
theorem review_set_minimax (v : G → I → Z) (measure : Z → ℝ)
    (R : G → Finset I) (m : G → ℕ) (hm : ∀ g,m g ≤ (R g).card)
    (F : Finset (Finset (G × I))) (hne : F.Nonempty)
    (hactual : ∀ S ∈ F,∀ q ∈ S,q.2 ∈ R q.1) :
    ∃ S ∈ F,
      (fixedQueries R (remainingOf R S)).toFinset = S ∧
      (∀ T ∈ F,
        potential v measure (remainingOf R S) (threshold (initialConfig R m) (remainingOf R S)) ≤
        potential v measure (remainingOf R T) (threshold (initialConfig R m) (remainingOf R T))) ∧
      Legal (AllowedRemaining R F) (initialConfig R m) (fixedPlan (fixedQueries R (remainingOf R S))) ∧
      worst v measure (initialConfig R m) (fixedPlan (fixedQueries R (remainingOf R S))) =
        potential v measure (remainingOf R S) (threshold (initialConfig R m) (remainingOf R S)) ∧
      ∀ p : Policy G I, Legal (AllowedRemaining R F) (initialConfig R m) p →
        potential v measure (remainingOf R S) (threshold (initialConfig R m) (remainingOf R S)) ≤
        worst v measure (initialConfig R m) p := by
  obtain ⟨T,hT,hmin,hlegal,heq,hlower⟩ := fixed_adaptive_minimax v measure (AllowedRemaining R F)
    (allowed_nonempty R F hne) (initialConfig R m) (initial_good R m hm) (allowed_subset R F)
  obtain ⟨S,hS,rfl⟩ := mem_image.mp hT
  refine ⟨S,hS,fixedQueries_exact_set R S (hactual S hS),?_,hlegal,heq,hlower⟩
  intro T hT
  exact hmin _ (mem_image.mpr ⟨T,hT,rfl⟩)

theorem threshold_formula (R : G → Finset I) (m : G → ℕ) (S : Finset (G × I)) (g : G) :
    threshold (initialConfig R m) (remainingOf R S) g =
      min (min (m g) ((R g).card-m g)) ((remainingOf R S g).card / 2) := rfl

end FusionDisjoint
