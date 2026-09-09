import Fusion.Basic

namespace Fusion
open Finset

/-- A fixed review set can certify a target only if no two opposite-target
    states have the same observed transcript. -/
def Certifies {X I : Type*} (S : Set I) (obs : X → I → Bool) (target : X → Bool) : Prop :=
  ∀ x z, (∀ i ∈ S, obs x i = obs z i) → target x = target z

theorem indistinguishable_obstruction {X I : Type*} (S : Set I)
    (obs : X → I → Bool) (target : X → Bool) (x z : X)
    (hobs : ∀ i ∈ S, obs x i = obs z i) (ht : target x ≠ target z) :
    ¬Certifies S obs target := by
  intro hc; exact ht (hc x z hobs)

/-- Payload-pair state space: one leaf and one of two target signs. -/
abbrev PairState (K : ℕ) := Fin K × Bool

/-- Querying one plus-payload record from each leaf determines the sign. -/
def payloadObs {K : ℕ} (x : PairState K) (i : Fin K) : Bool :=
  (decide (x.1 = i)) && x.2

theorem all_payloads_certify (K : ℕ) :
    Certifies Set.univ (@payloadObs K) (fun x => x.2) := by
  intro x z h
  by_cases hx : x.2 = true
  · have hh := h x.1 (Set.mem_univ _)
    simp [payloadObs,hx] at hh
    exact hx.trans hh.2.symm
  · have hx' : x.2 = false := Bool.eq_false_iff.mpr hx
    have hh := h z.1 (Set.mem_univ _)
    simp [payloadObs,hx'] at hh
    exact hx'.trans hh.symm

/-- Missing a leaf's payload query leaves both target signs indistinguishable. -/
theorem missing_payload_obstruction {K : ℕ} (S : Set (Fin K)) (leaf : Fin K)
    (hmiss : leaf ∉ S) :
    ¬Certifies S (@payloadObs K) (fun x => x.2) := by
  apply indistinguishable_obstruction S _ _ (leaf,true) (leaf,false)
  · intro i hi
    have hne : leaf ≠ i := by intro he; exact hmiss (he ▸ hi)
    simp [payloadObs,hne]
  · simp

/-- Arithmetic part of the intact-pair adversary: a payload query removes
    at most one pair, which is at most half when at least two remain. -/
theorem payload_retains_half (p : ℕ) (hp : 2 ≤ p) :
    (p+1)/2 ≤ p-1 := by omega

/-- A binary split has a branch retaining at least half of all intact pairs. -/
theorem split_retains_half (p q : ℕ) :
    (p+q+1)/2 ≤ p ∨ (p+q+1)/2 ≤ q := by omega

/-- Iterated halving retains at least 2^(k-t) pairs for t ≤ k.
    The halving hypothesis must be supplied by the query-game semantics. -/
theorem survival_power (p : ℕ → ℕ) (k : ℕ) (h0 : 2^k ≤ p 0)
    (hstep : ∀ t < k, p t ≤ 2*p (t+1)) :
    ∀ t ≤ k, 2^(k-t) ≤ p t := by
  intro t ht
  induction t with
  | zero => simpa using h0
  | succ t ih =>
    have htk : t < k := by omega
    have hi := ih (by omega)
    have hs := hstep t htk
    have hexp : k-t = (k-(t+1))+1 := by omega
    rw [hexp, pow_succ] at hi
    omega

/-- Adjacent-rank swaps realize coefficients +1 and -1 exactly. -/
theorem adjacent_rank_swap (r : ℤ) :
    ((r+1)-r=1) ∧ (r-(r+1) = -1) := by omega

theorem payload_complement_cancellation (x y : ℤ) :
    (1-x)-(1-y) = -(x-y) := by omega

theorem reported_budget_arithmetic :
    2^10 = (1024:ℕ) ∧ 4*2^10-2 = (4094:ℕ) ∧ 10+1=(11:ℕ) := by decide


/-- Tree queries reveal a property of the address. Payload queries test one
    address and one of its two signs. This includes the paper's path-state
    observation model after the stated complementation is decoded. -/
abbrev PairQuery (K : ℕ) (Tree : Type*) := Sum Tree (Fin K × Bool)

def pairObs {K : ℕ} {Tree : Type*} (treeObs : Fin K → Tree → Bool)
    (x : PairState K) : PairQuery K Tree → Bool
  | .inl t => treeObs x.1 t
  | .inr (leaf, sign) => decide (x.1 = leaf) && decide (x.2 = sign)

inductive ReviewPolicy (I : Type*) where
  | stop : Bool → ReviewPolicy I
  | ask : I → ReviewPolicy I → ReviewPolicy I → ReviewPolicy I

def policyDepth {I : Type*} : ReviewPolicy I → ℕ
  | .stop _ => 0
  | .ask _ p0 p1 => 1 + max (policyDepth p0) (policyDepth p1)

def policyRun {I X : Type*} (obs : X → I → Bool) : ReviewPolicy I → X → Bool
  | .stop b, _ => b
  | .ask i p0 p1, x => if obs x i then policyRun obs p1 x else policyRun obs p0 x

/-- Every exact fixed design must cover each payload pair, even with arbitrary
    additional address-only queries. -/
theorem fixed_pair_coverage {K : ℕ} {Tree : Type*}
    (treeObs : Fin K → Tree → Bool) (S : Set (PairQuery K Tree))
    (hc : Certifies S (pairObs treeObs) (fun x => x.2)) (leaf : Fin K) :
    Sum.inr (leaf,false) ∈ S ∨ Sum.inr (leaf,true) ∈ S := by
  by_contra h
  have h0 : Sum.inr (leaf,false) ∉ S := fun hh => h (Or.inl hh)
  have h1 : Sum.inr (leaf,true) ∉ S := fun hh => h (Or.inr hh)
  have heq : (true:Bool) = false := hc (leaf,true) (leaf,false) (by
    intro i hi
    cases i with
    | inl t => rfl
    | inr v =>
      obtain ⟨a,b⟩ := v
      by_cases ha : leaf = a
      · subst a
        cases b
        · exact False.elim (h0 hi)
        · exact False.elim (h1 hi)
      · simp [pairObs,ha])
  cases heq

/-- The fixed lower bound K is fully formalized in the abstract pair model. -/
theorem fixed_budget_lower {K : ℕ} {Tree : Type*} [DecidableEq Tree]
    (treeObs : Fin K → Tree → Bool) (S : Finset (PairQuery K Tree))
    (hc : Certifies (↑S) (pairObs treeObs) (fun x => x.2)) : K ≤ S.card := by
  classical
  have hchoose : ∀ leaf : Fin K, ∃ q : {q // q ∈ S},
      q.val = Sum.inr (leaf,false) ∨ q.val = Sum.inr (leaf,true) := by
    intro leaf
    rcases fixed_pair_coverage treeObs (↑S) hc leaf with h | h
    · exact ⟨⟨_,h⟩,Or.inl rfl⟩
    · exact ⟨⟨_,h⟩,Or.inr rfl⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro a b hab
    have hv := congrArg Subtype.val hab
    rcases hf a with ha | ha <;> rcases hf b with hb | hb <;>
      rw [ha,hb] at hv <;> cases hv <;> rfl
  simpa using Fintype.card_le_of_injective f hinj

/-- Exact adaptive certification of 2^k or more intact pairs needs more than
    k queries, for every choice of address-only tree observations. -/
theorem adaptive_pair_lower {K : ℕ} {Tree : Type*}
    (treeObs : Fin K → Tree → Bool) (k : ℕ) :
    ∀ (p : ReviewPolicy (PairQuery K Tree)) (S : Finset (Fin K)),
    policyDepth p ≤ k → 2^k ≤ S.card →
    ¬(∀ a ∈ S, ∀ b : Bool, policyRun (pairObs treeObs) p (a,b) = b) := by
  classical
  induction k with
  | zero =>
    intro p S hdepth hcard hcorrect
    have hne : S.Nonempty := card_pos.mp (by simpa using hcard)
    obtain ⟨a,ha⟩ := hne
    cases p with
    | stop b =>
      have h0 := hcorrect a ha false
      have h1 := hcorrect a ha true
      simp [policyRun] at h0 h1
      exact Bool.noConfusion (h0.symm.trans h1)
    | ask i p0 p1 => simp [policyDepth] at hdepth
  | succ k ih =>
    intro p S hdepth hcard hcorrect
    cases p with
    | stop b =>
      have hpow : 0 < (2:ℕ)^(k+1) := by positivity
      obtain ⟨a,ha⟩ := card_pos.mp (lt_of_lt_of_le hpow hcard)
      have h0 := hcorrect a ha false
      have h1 := hcorrect a ha true
      simp [policyRun] at h0 h1
      exact Bool.noConfusion (h0.symm.trans h1)
    | ask i p0 p1 =>
      have hd0 : policyDepth p0 ≤ k := by simp only [policyDepth] at hdepth; omega
      have hd1 : policyDepth p1 ≤ k := by simp only [policyDepth] at hdepth; omega
      cases i with
      | inl t =>
        let S0 := S.filter (fun a => treeObs a t = false)
        let S1 := S.filter (fun a => treeObs a t = true)
        have hsum : S0.card + S1.card = S.card := by
          have hh := filter_card_add_filter_neg_card_eq_card (s := S) (fun a => treeObs a t = false)
          simpa [S0,S1,Bool.not_eq_false] using hh
        have hsplit : 2^k ≤ S0.card ∨ 2^k ≤ S1.card := by
          rw [pow_succ] at hcard
          omega
        rcases hsplit with hs | hs
        · apply ih p0 S0 hd0 hs
          intro a ha b
          have hm := mem_filter.mp ha
          have hh := hcorrect a hm.1 b
          simpa [policyRun,pairObs,hm.2] using hh
        · apply ih p1 S1 hd1 hs
          intro a ha b
          have hm := mem_filter.mp ha
          have hh := hcorrect a hm.1 b
          simpa [policyRun,pairObs,hm.2] using hh
      | inr v =>
        obtain ⟨a0,b0⟩ := v
        let R := S.erase a0
        have hR : 2^k ≤ R.card := by
          have bound : S.card-1 ≤ R.card := by
            by_cases ha : a0 ∈ S
            · simp [R,card_erase_of_mem ha]
            · simp [R,erase_eq_of_not_mem ha]
          have hpow : 0 < (2:ℕ)^k := by positivity
          rw [pow_succ] at hcard
          omega
        apply ih p0 R hd0 hR
        intro a ha b
        have hm := mem_erase.mp ha
        have hh := hcorrect a hm.2 b
        simpa [policyRun,pairObs,hm.1] using hh

end Fusion
