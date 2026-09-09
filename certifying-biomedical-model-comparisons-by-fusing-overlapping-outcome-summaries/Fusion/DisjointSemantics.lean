import Fusion.DisjointGame

namespace FusionDisjoint
open Finset
variable {G I : Type*} [Fintype G] [Fintype I] [DecidableEq G] [DecidableEq I]

/-- Residual positive sets after the actual query execution. -/
def executeSelection : Config G I → Policy G I → (G → Finset I) → G → Finset I
  | _,.stop,A => A
  | c,.ask q p0 p1,A =>
      if q.2 ∈ c.remaining q.1 then
        if q.2 ∈ A q.1 then executeSelection (next c q true) p1 (eraseAt A q)
        else executeSelection (next c q false) p0 (eraseAt A q)
      else if q.2 ∈ c.known q.1 then executeSelection c p1 A else executeSelection c p0 A

theorem positive_union_step (c : Config G I) (A : G → Finset I) (q : G × I) :
    ∀ g, (next c q (decide (q.2 ∈ A q.1))).known g ∪ eraseAt A q g = c.known g ∪ A g := by
  intro g
  by_cases hg : g=q.1
  · subst g
    by_cases hi : q.2 ∈ A q.1
    · ext j
      by_cases hj : j=q.2 <;> simp [next,eraseAt,hi,hj]
    · simp [next,eraseAt,hi]
  · simp [next,eraseAt,hg]

/-- Every execution preserves the full underlying positive labeling as the
    union of its reviewed positives and its unreviewed positive completion. -/
theorem execution_label_preservation (c : Config G I) (p : Policy G I)
    (A : G → Finset I) (hA : Compatible c A) :
    Compatible (execute c p A) (executeSelection c p A) ∧
      ∀ g, (execute c p A).known g ∪ executeSelection c p A g = c.known g ∪ A g := by
  induction p generalizing c A with
  | stop => exact ⟨hA,fun _ => rfl⟩
  | ask q p0 p1 ih0 ih1 =>
    by_cases hq : q.2 ∈ c.remaining q.1
    · have hc := observed_compatible c A hA q
      have hu := positive_union_step c A q
      by_cases hi : q.2 ∈ A q.1
      · simp only [hi,decide_true] at hc hu
        have ih := ih1 (next c q true) (eraseAt A q) hc
        refine ⟨?_,?_⟩
        · simpa only [execute,executeSelection,if_pos hq,if_pos hi] using ih.1
        · intro g
          simpa only [execute,executeSelection,if_pos hq,if_pos hi] using (ih.2 g).trans (hu g)
      · simp only [hi,decide_false] at hc hu
        have ih := ih0 (next c q false) (eraseAt A q) hc
        refine ⟨?_,?_⟩
        · simpa only [execute,executeSelection,if_pos hq,if_neg hi] using ih.1
        · intro g
          simpa only [execute,executeSelection,if_pos hq,if_neg hi] using (ih.2 g).trans (hu g)
    · by_cases hk : q.2 ∈ c.known q.1
      · simpa only [execute,executeSelection,if_neg hq,if_pos hk] using ih1 c A hA
      · simpa only [execute,executeSelection,if_neg hq,if_neg hk] using ih0 c A hA

/-- Known target contributions cancel from completion differences. -/
theorem known_contribution_cancels {Z : Type*} [AddCommGroup Z] (known a b : Z) :
    (known+a)-(known+b)=a-b := by simp

/-- The paper's omitted nonemptiness condition is necessary: downward
    closure alone can hold without any available minimizing review set. -/
theorem empty_review_family {J : Type*} [DecidableEq J] :
    (∀ S ∈ (∅ : Finset (Finset J)), ∀ T, T ⊆ S → T ∈ (∅ : Finset (Finset J))) ∧
    ¬(∃ S, S ∈ (∅ : Finset (Finset J))) := by simp

end FusionDisjoint
