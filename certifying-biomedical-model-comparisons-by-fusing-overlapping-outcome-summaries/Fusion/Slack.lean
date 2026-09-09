import Fusion.Disjoint
import Mathlib.Data.Fintype.Basic

namespace FusionSlack
open Finset
variable {I Z : Type*} [DecidableEq I] [AddCommGroup Z]

/-- There are enough distinct binary slack records, not merely an integer slack count. -/
theorem slack_subsets (L U m : ℕ) (hLU : L ≤ U) :
    (L ≤ m ∧ m ≤ U) ↔ ∃ B : Finset (Fin (U-L)),m+B.card=U := by
  constructor
  · intro h
    have hs : U-m ≤ (univ : Finset (Fin (U-L))).card := by simp; omega
    obtain ⟨B,_,hB⟩ := exists_subset_card_eq hs
    exact ⟨B,by omega⟩
  · rintro ⟨B,hB⟩
    have hs : B.card ≤ U-L := by simpa using card_le_card (subset_univ B)
    omega

/-- Generic zero-coefficient target preservation for any number of slack records. -/
theorem zero_slack_target {J : Type*} (v : I → Z) (A : Finset I) (B : Finset J) :
    (∑ i ∈ A,v i)+(∑ _i ∈ B,(0:Z)) = ∑ i ∈ A,v i := by simp

/-- Feasible target sets are identical after every allowed original-record
    observation transcript. `observed` can encode any such transcript predicate. -/
theorem transcript_target_equivalence (R : Finset I) (v : I → Z)
    (L U : ℕ) (hLU : L ≤ U) (observed : Finset I → Prop) (z : Z) :
    (∃ A ⊆ R,L ≤ A.card ∧ A.card ≤ U ∧ observed A ∧ (∑ i ∈ A,v i)=z) ↔
    (∃ A ⊆ R,∃ B : Finset (Fin (U-L)),A.card+B.card=U ∧ observed A ∧
      (∑ i ∈ A,v i)+(∑ _i ∈ B,(0:Z))=z) := by
  constructor
  · rintro ⟨A,hA,hl,hu,ho,hz⟩
    obtain ⟨B,hB⟩ := (slack_subsets L U A.card hLU).mp ⟨hl,hu⟩
    exact ⟨A,hA,B,hB,ho,by simpa using hz⟩
  · rintro ⟨A,hA,B,hB,ho,hz⟩
    have h := (slack_subsets L U A.card hLU).mpr ⟨B,hB⟩
    exact ⟨A,hA,h.1,h.2,ho,by simpa using hz⟩

/-- Independent interval totals have independent slack labelings in all groups. -/
theorem grouped_slack_encoding {G : Type*} (R A : G → Finset I) (L U : G → ℕ)
    (hLU : ∀ g,L g ≤ U g) :
    (∀ g,A g ⊆ R g ∧ L g ≤ (A g).card ∧ (A g).card ≤ U g) ↔
    ∃ B : (g : G) → Finset (Fin (U g-L g)),∀ g,A g ⊆ R g ∧ (A g).card+(B g).card=U g := by
  constructor
  · intro h
    have hs (g : G) := (slack_subsets (L g) (U g) (A g).card (hLU g)).mp (h g).2
    choose B hB using hs
    exact ⟨B,fun g => ⟨(h g).1,hB g⟩⟩
  · rintro ⟨B,h⟩ g
    exact ⟨(h g).1,(slack_subsets (L g) (U g) (A g).card (hLU g)).mpr ⟨B g,(h g).2⟩⟩

end FusionSlack
