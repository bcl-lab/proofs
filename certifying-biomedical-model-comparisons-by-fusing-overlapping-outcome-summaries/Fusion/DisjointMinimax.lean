import Fusion.DisjointGame

namespace FusionDisjoint
open Finset
variable {G I Z : Type*} [Fintype G] [Fintype I] [DecidableEq G] [DecidableEq I]
  [AddCommGroup Z]

noncomputable def completionCandidates (c : Config G I) : Finset (G → Finset I) := by
  classical
  exact univ.filter (Compatible c)

theorem mem_completionCandidates (c : Config G I) (A : G → Finset I) :
    A ∈ completionCandidates c ↔ Compatible c A := by
  classical
  simp [completionCandidates]

theorem completionCandidates_nonempty (c : Config G I) (hc : Good c) :
    (completionCandidates c).Nonempty := by
  obtain ⟨A,hA⟩ := compatible_exists c hc
  exact ⟨A,(mem_completionCandidates c A).mpr hA⟩

/-- Worst completion diameter over fixed feasible input labelings. -/
noncomputable def worst (v : G → I → Z) (measure : Z → ℝ) (c : Config G I) (p : Policy G I) : ℝ :=
  maximum (completionCandidates c)
    (fun A => diameter v measure (execute c p A).remaining (execute c p A).pos)

theorem good_diameter (v : G → I → Z) (measure : Z → ℝ) (c : Config G I) (hc : Good c) :
    diameter v measure c.remaining c.pos = potential v measure c.remaining (fun g => min (c.pos g) (c.neg g)) := by
  rw [diameter_eq_potential v measure c.remaining c.pos (by intro g; have hh := hc g; omega)]
  congr 1
  funext g
  have hh := hc g
  omega

theorem balanced_diameter (v : G → I → Z) (measure : Z → ℝ) (initial c : Config G I)
    (hc : Good c) (hb : Balanced initial c) :
    diameter v measure c.remaining c.pos = potential v measure c.remaining (threshold initial c.remaining) := by
  rw [good_diameter v measure c hc]
  congr 1
  exact funext hb

theorem diameter_upper (v : G → I → Z) (measure : Z → ℝ) (initial c : Config G I)
    (hc : Good c) (hd : Dominated initial c) :
    diameter v measure c.remaining c.pos ≤ potential v measure c.remaining (threshold initial c.remaining) := by
  rw [good_diameter v measure c hc]
  apply potential_mono
  intro g
  have hh := hc g
  have hb := hd g
  unfold threshold
  omega

set_option maxHeartbeats 1000000 in
/-- The adaptive lower bound is attained by an actual input witness from
    the majority construction and compared with the minimum over allowed sets. -/
theorem policy_lower (v : G → I → Z) (measure : Z → ℝ)
    (F : Finset (G → Finset I)) (c : Config G I) (hc : Good c) (b : ℝ)
    (hb : ∀ R ∈ F, b ≤ potential v measure R (threshold c R))
    (p : Policy G I) (hp : Legal F c p) : b ≤ worst v measure c p := by
  obtain ⟨A,hA,hg,hbal,hF⟩ := adversary_input F c c hc (balanced_initial c hc) p hp
  calc
    b ≤ potential v measure (execute c p A).remaining (threshold c (execute c p A).remaining) := hb _ hF
    _ = diameter v measure (execute c p A).remaining (execute c p A).pos :=
      (balanced_diameter v measure c (execute c p A) hg hbal).symm
    _ ≤ worst v measure c p := by
      unfold worst
      exact le_maximum (completionCandidates c)
        (fun B => diameter v measure (execute c p B).remaining (execute c p B).pos) A
        ((mem_completionCandidates c A).mpr hA)

def fixedPlan : List (G × I) → Policy G I
  | [] => .stop
  | q::qs => .ask q (fixedPlan qs) (fixedPlan qs)

def eraseAll : (G → Finset I) → List (G × I) → G → Finset I
  | R,[] => R
  | R,q::qs => eraseAll (eraseAt R q) qs

theorem eraseAt_of_not_mem (R : G → Finset I) (q : G × I) (h : q.2 ∉ R q.1) : eraseAt R q = R := by
  funext g
  by_cases hg : g=q.1
  · subst g; simp [eraseAt,h]
  · simp [eraseAt,hg]

theorem execute_fixed_remaining (c : Config G I) (qs : List (G × I)) (A : G → Finset I) :
    (execute c (fixedPlan qs) A).remaining = eraseAll c.remaining qs := by
  induction qs generalizing c A with
  | nil => rfl
  | cons q qs ih =>
    by_cases hq : q.2 ∈ c.remaining q.1
    · by_cases hm : q.2 ∈ A q.1 <;>
        simp [fixedPlan,execute,hq,hm,ih,eraseAll,next]
    · by_cases hk : q.2 ∈ c.known q.1 <;>
        simp [fixedPlan,execute,hq,hk,ih,eraseAll,eraseAt_of_not_mem _ _ hq]

theorem fixedPlan_legal (F : Finset (G → Finset I)) (c : Config G I) (qs : List (G × I))
    (hF : eraseAll c.remaining qs ∈ F) : Legal F c (fixedPlan qs) := by
  induction qs generalizing c with
  | nil => exact hF
  | cons q qs ih =>
    by_cases hq : q.2 ∈ c.remaining q.1
    · simp only [fixedPlan,Legal,if_pos hq]
      exact ⟨fun _ => ih (next c q false) hF,fun _ => ih (next c q true) hF⟩
    · have hf : eraseAll c.remaining qs ∈ F := by
        simpa only [eraseAll,eraseAt_of_not_mem _ _ hq] using hF
      by_cases hk : q.2 ∈ c.known q.1 <;>
        simpa [fixedPlan,Legal,hq,hk] using ih c hf

theorem mem_eraseAt (R : G → Finset I) (q : G × I) (g : G) (i : I) :
    i ∈ eraseAt R q g ↔ i ∈ R g ∧ (g,i) ≠ q := by
  rcases q with ⟨h,j⟩
  by_cases hg : g=h
  · subst g
    simp [eraseAt,and_comm]
  · simp [eraseAt,hg]

theorem mem_eraseAll (R : G → Finset I) (qs : List (G × I)) (g : G) (i : I) :
    i ∈ eraseAll R qs g ↔ i ∈ R g ∧ (g,i) ∉ qs := by
  induction qs generalizing R with
  | nil => simp [eraseAll]
  | cons q qs ih =>
    rw [eraseAll,ih,mem_eraseAt]
    simp only [List.mem_cons,not_or,and_assoc]

noncomputable def fixedQueries (R T : G → Finset I) : List (G × I) :=
  (univ.filter (fun q : G × I => q.2 ∈ R q.1 ∧ q.2 ∉ T q.1)).toList

theorem mem_fixedQueries (R T : G → Finset I) (q : G × I) :
    q ∈ fixedQueries R T ↔ q.2 ∈ R q.1 ∧ q.2 ∉ T q.1 := by
  simp [fixedQueries]

theorem eraseAll_fixed (R T : G → Finset I) (h : ∀ g, T g ⊆ R g) :
    eraseAll R (fixedQueries R T) = T := by
  funext g
  ext i
  rw [mem_eraseAll,mem_fixedQueries]
  by_cases hi : i ∈ T g
  · simp [hi,h g hi]
  · simp [hi]

/-- A fixed set achieves its displayed potential as an upper bound, with
    the same actual-input execution semantics used for the adaptive lower bound. -/
theorem fixed_upper (v : G → I → Z) (measure : Z → ℝ)
    (F : Finset (G → Finset I)) (c : Config G I) (hc : Good c)
    (T : G → Finset I) (hT : T ∈ F) (hsub : ∀ g, T g ⊆ c.remaining g) :
    Legal F c (fixedPlan (fixedQueries c.remaining T)) ∧
      worst v measure c (fixedPlan (fixedQueries c.remaining T)) ≤ potential v measure T (threshold c T) := by
  have hlegal := fixedPlan_legal F c (fixedQueries c.remaining T)
    (by rw [eraseAll_fixed _ _ hsub]; exact hT)
  refine ⟨hlegal,?_⟩
  apply maximum_le _ _ (completionCandidates_nonempty c hc)
  intro A hA
  have hi := execution_invariants F c c hc (dominated_self c) _ hlegal A ((mem_completionCandidates c A).mp hA)
  have hu := diameter_upper v measure c (execute c (fixedPlan (fixedQueries c.remaining T)) A) hi.1 hi.2.1
  have hr : (execute c (fixedPlan (fixedQueries c.remaining T)) A).remaining = T := by
    rw [execute_fixed_remaining,eraseAll_fixed _ _ hsub]
  simpa only [hr] using hu

/-- Supplementary Equation S8. The minimum over permitted remaining sets
    equals the optimal worst-case diameter for both fixed and all finite
    deterministic adaptive policies. Repeated queries are allowed and decoded.
    Since `measure` is arbitrary, the statement includes every norm. -/
theorem fixed_adaptive_minimax (v : G → I → Z) (measure : Z → ℝ)
    (F : Finset (G → Finset I)) (hne : F.Nonempty) (c : Config G I) (hc : Good c)
    (hsub : ∀ T ∈ F, ∀ g, T g ⊆ c.remaining g) :
    ∃ T ∈ F,
      (∀ R ∈ F, potential v measure T (threshold c T) ≤ potential v measure R (threshold c R)) ∧
      Legal F c (fixedPlan (fixedQueries c.remaining T)) ∧
      worst v measure c (fixedPlan (fixedQueries c.remaining T)) = potential v measure T (threshold c T) ∧
      ∀ p : Policy G I, Legal F c p → potential v measure T (threshold c T) ≤ worst v measure c p := by
  obtain ⟨T,hT,hmin⟩ := exists_min_image F (fun R => potential v measure R (threshold c R)) hne
  have hlower : ∀ p : Policy G I, Legal F c p → potential v measure T (threshold c T) ≤ worst v measure c p :=
    fun p hp => policy_lower v measure F c hc _ hmin p hp
  obtain ⟨hlegal,hupper⟩ := fixed_upper v measure F c hc T hT (hsub T hT)
  exact ⟨T,hT,hmin,hlegal,le_antisymm hupper (hlower _ hlegal),hlower⟩

end FusionDisjoint
