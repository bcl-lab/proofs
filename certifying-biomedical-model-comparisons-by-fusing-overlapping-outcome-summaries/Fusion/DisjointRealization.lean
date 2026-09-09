import Fusion.DisjointSemantics

namespace FusionDisjoint
open Finset
variable {G I : Type*} [Fintype G] [Fintype I] [DecidableEq G] [DecidableEq I]

/-- Every residual completion at a reached leaf is realized by a fixed
    compatible initial labeling reaching that same leaf state. -/
theorem residual_realization (c : Config G I) (hc : Good c) (p : Policy G I)
    (A : G → Finset I) (hA : Compatible c A) (B : G → Finset I)
    (hB : Compatible (execute c p A) B) :
    ∃ C,Compatible c C ∧ execute c p C=execute c p A ∧ executeSelection c p C=B := by
  induction p generalizing c A B with
  | stop => exact ⟨B,hB,rfl,rfl⟩
  | ask q p0 p1 ih0 ih1 =>
    by_cases hq : q.2 ∈ c.remaining q.1
    · have hcan := observed_can c hc A hA q hq
      have hcomp := observed_compatible c A hA q
      by_cases hi : q.2 ∈ A q.1
      · simp only [hi,decide_true] at hcan hcomp
        have hgood := next_good c hc q hq true hcan
        have hB' : Compatible (execute (next c q true) p1 (eraseAt A q)) B := by
          simpa only [execute,if_pos hq,if_pos hi] using hB
        obtain ⟨C,hC,he,hsel⟩ := ih1 (next c q true) hgood (eraseAt A q) hcomp B hB'
        obtain ⟨D,hD,hd,herase⟩ := extend_completion c hc q hq true hcan C hC
        have hd' : q.2 ∈ D q.1 := of_decide_eq_true hd
        refine ⟨D,hD,?_,?_⟩
        · simpa only [execute,if_pos hq,if_pos hi,if_pos hd',herase] using he
        · simpa only [executeSelection,if_pos hq,if_pos hd',herase] using hsel
      · simp only [hi,decide_false] at hcan hcomp
        have hgood := next_good c hc q hq false hcan
        have hB' : Compatible (execute (next c q false) p0 (eraseAt A q)) B := by
          simpa only [execute,if_pos hq,if_neg hi] using hB
        obtain ⟨C,hC,he,hsel⟩ := ih0 (next c q false) hgood (eraseAt A q) hcomp B hB'
        obtain ⟨D,hD,hd,herase⟩ := extend_completion c hc q hq false hcan C hC
        have hd' : q.2 ∉ D q.1 := of_decide_eq_false hd
        refine ⟨D,hD,?_,?_⟩
        · simpa only [execute,if_pos hq,if_neg hi,if_neg hd',herase] using he
        · simpa only [executeSelection,if_pos hq,if_neg hd',herase] using hsel
    · by_cases hk : q.2 ∈ c.known q.1
      · simp only [execute,if_neg hq,if_pos hk] at hB
        obtain ⟨C,hC,he,hsel⟩ := ih1 c hc A hA B hB
        exact ⟨C,hC,by simpa [execute,hq,hk] using he,by simpa [executeSelection,hq,hk] using hsel⟩
      · simp only [execute,if_neg hq,if_neg hk] at hB
        obtain ⟨C,hC,he,hsel⟩ := ih0 c hc A hA B hB
        exact ⟨C,hC,by simpa [execute,hq,hk] using he,by simpa [executeSelection,hq,hk] using hsel⟩

end FusionDisjoint
