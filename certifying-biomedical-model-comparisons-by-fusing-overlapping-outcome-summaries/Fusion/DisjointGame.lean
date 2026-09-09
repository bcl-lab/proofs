import Fusion.DisjointDiameter

namespace FusionDisjoint
open Finset
variable {G I Z : Type*} [Fintype G] [Fintype I] [DecidableEq G] [DecidableEq I]
  [AddCommGroup Z]

structure Config (G I : Type*) where
  remaining : G → Finset I
  pos : G → ℕ
  neg : G → ℕ
  known : G → Finset I

def Good (c : Config G I) : Prop := ∀ g, c.pos g+c.neg g = (c.remaining g).card

def Compatible (c : Config G I) (A : G → Finset I) : Prop :=
  ∀ g, A g ⊆ c.remaining g ∧ (A g).card = c.pos g

def eraseAt (R : G → Finset I) (q : G × I) : G → Finset I :=
  fun g => if g=q.1 then (R g).erase q.2 else R g

def next (c : Config G I) (q : G × I) (b : Bool) : Config G I where
  remaining := eraseAt c.remaining q
  pos := fun g => if g=q.1 ∧ b=true then c.pos g-1 else c.pos g
  neg := fun g => if g=q.1 ∧ b=false then c.neg g-1 else c.neg g
  known := fun g => if g=q.1 ∧ b=true then insert q.2 (c.known g) else c.known g

def CanAnswer (c : Config G I) (q : G × I) (b : Bool) : Prop :=
  if b then 0 < c.pos q.1 else 0 < c.neg q.1

theorem compatible_exists (c : Config G I) (hc : Good c) : ∃ A, Compatible c A := by
  classical
  have h (g : G) : ∃ A ⊆ c.remaining g, A.card = c.pos g :=
    exists_subset_card_eq (by have hh := hc g; omega)
  choose A ha hs using h
  exact ⟨A,fun g => ⟨ha g,hs g⟩⟩

theorem next_good (c : Config G I) (hc : Good c) (q : G × I)
    (hq : q.2 ∈ c.remaining q.1) (b : Bool) (hb : CanAnswer c q b) : Good (next c q b) := by
  intro g
  by_cases hg : g=q.1
  · subst g
    have hh := hc q.1
    have he := card_erase_of_mem hq
    cases b <;> simp [CanAnswer] at hb <;> simp [next,eraseAt] <;> omega
  · simpa [next,eraseAt,hg] using hc g

theorem observed_can (c : Config G I) (hc : Good c) (A : G → Finset I)
    (hA : Compatible c A) (q : G × I) (hq : q.2 ∈ c.remaining q.1) :
    CanAnswer c q (decide (q.2 ∈ A q.1)) := by
  by_cases hm : q.2 ∈ A q.1
  · simp only [hm,decide_true,CanAnswer,↓reduceIte]
    have hp := card_pos.mpr ⟨q.2,hm⟩
    rw [(hA q.1).2] at hp
    exact hp
  · simp only [hm,decide_false,CanAnswer,Bool.false_eq_true,↓reduceIte]
    have hs : A q.1 ⊂ c.remaining q.1 := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨(hA q.1).1,?_⟩
      intro he; exact hm (he ▸ hq)
    have hh := card_lt_card hs
    have hg := hc q.1
    rw [(hA q.1).2] at hh
    omega

theorem observed_compatible (c : Config G I) (A : G → Finset I) (hA : Compatible c A)
    (q : G × I) : Compatible (next c q (decide (q.2 ∈ A q.1))) (eraseAt A q) := by
  intro g
  by_cases hg : g=q.1
  · subst g
    constructor
    · simpa [eraseAt,next] using erase_subset_erase q.2 (hA q.1).1
    · by_cases hm : q.2 ∈ A q.1
      · simp [eraseAt,next,hm,card_erase_of_mem hm,(hA q.1).2]
      · simp [eraseAt,next,hm,(hA q.1).2]
  · simpa [eraseAt,next,hg] using hA g

/-- A residual completion can be extended by the selected feasible answer. -/
theorem extend_completion (c : Config G I) (hc : Good c) (q : G × I)
    (hq : q.2 ∈ c.remaining q.1) (b : Bool) (hb : CanAnswer c q b)
    (A : G → Finset I) (hA : Compatible (next c q b) A) :
    ∃ B, Compatible c B ∧ decide (q.2 ∈ B q.1) = b ∧ eraseAt B q = A := by
  classical
  have hnot : q.2 ∉ A q.1 := by
    intro hm
    have hh := (hA q.1).1 hm
    simpa [next,eraseAt] using hh
  cases b with
  | false =>
    refine ⟨A,?_,by simp [hnot],?_⟩
    · intro g
      by_cases hg : g=q.1
      · subst g
        have hh := hA q.1
        simp only [next,eraseAt,↓reduceIte,and_false,Bool.false_eq_true] at hh
        exact ⟨hh.1.trans (erase_subset _ _),hh.2⟩
      · simpa [next,eraseAt,hg] using hA g
    · funext g
      by_cases hg : g=q.1
      · subst g; simp [eraseAt,hnot]
      · simp [eraseAt,hg]
  | true =>
    let B : G → Finset I := fun g => if g=q.1 then insert q.2 (A g) else A g
    refine ⟨B,?_,by simp [B],?_⟩
    · intro g
      by_cases hg : g=q.1
      · subst g
        have hh := hA q.1
        have hp : 0 < c.pos q.1 := hb
        constructor
        · simp only [B,if_pos rfl]
          apply insert_subset hq
          exact hh.1.trans (by simp [next,eraseAt]; exact erase_subset _ _)
        · simp only [B,if_pos rfl]
          rw [card_insert_of_not_mem hnot]
          simp only [next,↓reduceIte,and_self] at hh
          omega
      · simpa [B,next,eraseAt,hg] using hA g
    · funext g
      by_cases hg : g=q.1
      · subst g; simp [eraseAt,B,hnot]
      · simp [eraseAt,B,hg]

def Dominated (initial c : Config G I) : Prop :=
  ∀ g, c.pos g ≤ initial.pos g ∧ c.neg g ≤ initial.neg g

def threshold (initial : Config G I) (R : G → Finset I) (g : G) : ℕ :=
  min (min (initial.pos g) (initial.neg g)) ((R g).card/2)

def Balanced (initial c : Config G I) : Prop :=
  ∀ g, min (c.pos g) (c.neg g) = threshold initial c.remaining g

theorem dominated_self (c : Config G I) : Dominated c c := fun _ => ⟨le_rfl,le_rfl⟩
theorem dominated_next (initial c : Config G I) (h : Dominated initial c) (q : G × I) (b : Bool) :
    Dominated initial (next c q b) := by
  intro g
  have hh := h g
  simp only [next]
  split_ifs <;> omega

theorem balanced_initial (c : Config G I) (hc : Good c) : Balanced c c := by
  intro g
  have hh := hc g
  unfold threshold
  omega

def majority (c : Config G I) (q : G × I) : Bool := decide (c.neg q.1 ≤ c.pos q.1)

theorem majority_can (c : Config G I) (hc : Good c) (q : G × I)
    (hq : q.2 ∈ c.remaining q.1) : CanAnswer c q (majority c q) := by
  have hh := hc q.1
  have hp := card_pos.mpr ⟨q.2,hq⟩
  by_cases hm : c.neg q.1 ≤ c.pos q.1 <;> simp [majority,CanAnswer,hm] <;> omega

theorem balanced_next (initial c : Config G I) (hc : Good c) (hbal : Balanced initial c)
    (q : G × I) (hq : q.2 ∈ c.remaining q.1) : Balanced initial (next c q (majority c q)) := by
  intro g
  by_cases hg : g=q.1
  · subst g
    have hh := hc q.1
    have hi := hbal q.1
    have he := card_erase_of_mem hq
    have hp := card_pos.mpr ⟨q.2,hq⟩
    have hm := Fusion.majority_step (c.pos q.1) (c.neg q.1) (by omega)
    unfold threshold at hi ⊢
    by_cases hle : c.neg q.1 ≤ c.pos q.1 <;>
      simp [next,eraseAt,majority,hle] <;> simp [hle] at hm <;> omega
  · simpa [next,eraseAt,threshold,hg] using hbal g

inductive Policy (G I : Type*) where
  | stop : Policy G I
  | ask : G × I → Policy G I → Policy G I → Policy G I

def execute : Config G I → Policy G I → (G → Finset I) → Config G I
  | c,.stop,_ => c
  | c,.ask q p0 p1,A =>
      if q.2 ∈ c.remaining q.1 then
        if q.2 ∈ A q.1 then execute (next c q true) p1 (eraseAt A q)
        else execute (next c q false) p0 (eraseAt A q)
      else if q.2 ∈ c.known q.1 then execute c p1 A else execute c p0 A

/-- Only feasible branches constrain the policy. Repeated queries read their
    recorded answer and do not consume another label or change the state. -/
def Legal (F : Finset (G → Finset I)) : Config G I → Policy G I → Prop
  | c,.stop => c.remaining ∈ F
  | c,.ask q p0 p1 =>
      if q.2 ∈ c.remaining q.1 then
        (CanAnswer c q false → Legal F (next c q false) p0) ∧
        (CanAnswer c q true → Legal F (next c q true) p1)
      else if q.2 ∈ c.known q.1 then Legal F c p1 else Legal F c p0

theorem execution_invariants (F : Finset (G → Finset I)) (initial c : Config G I)
    (hc : Good c) (hd : Dominated initial c) (p : Policy G I) (hp : Legal F c p)
    (A : G → Finset I) (hA : Compatible c A) :
    Good (execute c p A) ∧ Dominated initial (execute c p A) ∧ (execute c p A).remaining ∈ F := by
  induction p generalizing c A with
  | stop => exact ⟨hc,hd,hp⟩
  | ask q p0 p1 ih0 ih1 =>
    by_cases hq : q.2 ∈ c.remaining q.1
    · simp only [Legal,if_pos hq] at hp
      have hb := observed_can c hc A hA q hq
      have hAc := observed_compatible c A hA q
      by_cases hm : q.2 ∈ A q.1
      · simp only [hm,decide_true] at hb hAc
        simpa only [execute,if_pos hq,if_pos hm] using
          ih1 (next c q true) (next_good c hc q hq true hb) (dominated_next initial c hd q true)
            (hp.2 hb) (eraseAt A q) hAc
      · simp only [hm,decide_false] at hb hAc
        simpa only [execute,if_pos hq,if_neg hm] using
          ih0 (next c q false) (next_good c hc q hq false hb) (dominated_next initial c hd q false)
            (hp.1 hb) (eraseAt A q) hAc
    · by_cases hk : q.2 ∈ c.known q.1
      · simp only [Legal,if_neg hq,if_pos hk] at hp
        simpa only [execute,if_neg hq,if_pos hk] using ih1 c hc hd hp A hA
      · simp only [Legal,if_neg hq,if_neg hk] at hp
        simpa only [execute,if_neg hq,if_neg hk] using ih0 c hc hd hp A hA

/-- The majority transcript is realized by one fixed compatible labeling,
    including policies that repeat queries or stop at different depths. -/
theorem adversary_input (F : Finset (G → Finset I)) (initial c : Config G I)
    (hc : Good c) (hbal : Balanced initial c) (p : Policy G I) (hp : Legal F c p) :
    ∃ A, Compatible c A ∧ Good (execute c p A) ∧ Balanced initial (execute c p A) ∧
      (execute c p A).remaining ∈ F := by
  induction p generalizing c with
  | stop =>
    obtain ⟨A,hA⟩ := compatible_exists c hc
    exact ⟨A,hA,hc,hbal,hp⟩
  | ask q p0 p1 ih0 ih1 =>
    by_cases hq : q.2 ∈ c.remaining q.1
    · simp only [Legal,if_pos hq] at hp
      have hb := majority_can c hc q hq
      have hg := next_good c hc q hq (majority c q) hb
      have hbal' := balanced_next initial c hc hbal q hq
      cases hm : majority c q
      · rw [hm] at hb hg hbal'
        obtain ⟨A,hA,hg',hbal'',hf⟩ := ih0 (next c q false) hg hbal' (hp.1 hb)
        obtain ⟨B,hB,hobs,herase⟩ := extend_completion c hc q hq false hb A hA
        have hobs' : q.2 ∉ B q.1 := by simpa using hobs
        refine ⟨B,hB,?_⟩
        simpa only [execute,if_pos hq,if_neg hobs',herase] using And.intro hg' (And.intro hbal'' hf)
      · rw [hm] at hb hg hbal'
        obtain ⟨A,hA,hg',hbal'',hf⟩ := ih1 (next c q true) hg hbal' (hp.2 hb)
        obtain ⟨B,hB,hobs,herase⟩ := extend_completion c hc q hq true hb A hA
        have hobs' : q.2 ∈ B q.1 := by simpa using hobs
        refine ⟨B,hB,?_⟩
        simpa only [execute,if_pos hq,if_pos hobs',herase] using And.intro hg' (And.intro hbal'' hf)
    · by_cases hk : q.2 ∈ c.known q.1
      · simp only [Legal,if_neg hq,if_pos hk] at hp
        obtain ⟨A,hA,hr⟩ := ih1 c hc hbal hp
        exact ⟨A,hA,by simpa only [execute,if_neg hq,if_pos hk] using hr⟩
      · simp only [Legal,if_neg hq,if_neg hk] at hp
        obtain ⟨A,hA,hr⟩ := ih0 c hc hbal hp
        exact ⟨A,hA,by simpa only [execute,if_neg hq,if_neg hk] using hr⟩

end FusionDisjoint
