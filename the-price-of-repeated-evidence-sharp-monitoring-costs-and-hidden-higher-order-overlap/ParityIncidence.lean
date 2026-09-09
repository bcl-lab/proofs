import ParityCore
import OverlapReconstruction

set_option maxHeartbeats 2000000
namespace ParityIncidence
open OverlapReconstruction
open RepeatedEvidenceCore

def degree : (n : Nat) → Cube n → Nat
  | 0, _ => 0
  | n+1, (b,x) => (if b then 1 else 0) + degree n x

def toggle : (n : Nat) → Bool → Cube n → Bool
  | 0, b, _ => b
  | n+1, b, (c,x) => toggle n (if c then !b else b) x

/-- Exact-pattern multiplicity, with r already included studies. -/
def multiplicity : (n : Nat) → Nat → Bool → Cube n → Int
  | 0, r, b, _ => if b then 0 else (r : Int)
  | n+1, r, b, (c,x) => if c then multiplicity n (r+1) (!b) x else multiplicity n r b x

theorem degree_le (n : Nat) (x : Cube n) : degree n x ≤ n := by
  induction n with
  | zero => simp [degree]
  | succ n ih => rcases x with ⟨b,x⟩; cases b <;> simp [degree] <;> have := ih x <;> omega

theorem toggle_not (n : Nat) (b : Bool) (x : Cube n) : toggle n (!b) x = !(toggle n b x) := by
  induction n with
  | zero => rfl
  | succ n ih => rcases x with ⟨c,x⟩; cases c <;> simp [toggle, ih]

theorem zeta_add (n : Nat) (f g : Cube n → Int) (x : Cube n) :
    zeta n (fun y => f y+g y) x = zeta n f x+zeta n g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b
    · change zeta n (fun y => (f (false,y)+g (false,y))+(f (true,y)+g (true,y))) x = _
      have he : (fun y => (f (false,y)+g (false,y))+(f (true,y)+g (true,y))) =
          (fun y => (f (false,y)+f (true,y))+(g (false,y)+g (true,y))) := by
        funext y; omega
      rw [he,ih]
      rfl
    · exact ih (fun y => f (true,y)) (fun y => g (true,y)) x

/-- Exact identification of every intersection query with the weighted parity
recurrence, including arbitrary queried subsets and all dimensions. -/
theorem intersection_is_parityWeight (n r : Nat) (b : Bool) (x : Cube n) :
    zeta n (multiplicity n r b) x =
      (parityWeight (n-degree n x) (r+degree n x) (toggle n b x) : Int) := by
  induction n generalizing r b with
  | zero => cases b <;> simp [zeta,multiplicity,degree,toggle,parityWeight]
  | succ n ih =>
    rcases x with ⟨c,x⟩
    cases c
    · change zeta n (fun y => multiplicity n r b y + multiplicity n (r+1) (!b) y) x = _
      rw [zeta_add,ih,ih,toggle_not]
      have hd := degree_le n x
      have he : n+1-degree n x = (n-degree n x)+1 := by omega
      simp only [degree, Bool.false_eq_true, if_false, Nat.zero_add, toggle]
      rw [he, parityWeight]
      have hr : r+1+degree n x = r+degree n x+1 := by omega
      rw [hr]
      simp
    · change zeta n (multiplicity n (r+1) (!b)) x = _
      rw [ih]
      simp only [degree, if_true, toggle]
      have he : n+1-(1+degree n x) = n-degree n x := by omega
      have hr : r+(1+degree n x) = r+1+degree n x := by omega
      rw [he,hr]

/-- General matched intersection counts, now for actual binary incidence
patterns rather than an unconnected recurrence. -/
theorem all_intersection_counts (m : Nat) (x : Cube m) (h : degree m x+2 ≤ m) (b : Bool) :
    zeta m (multiplicity m 0 b) x = ((m+degree m x)*2^(m-degree m x-2) : Nat) := by
  rw [intersection_is_parityWeight]
  simp only [Nat.zero_add]
  rw [overlap_count_formula m (degree m x) h]

theorem parity_systems_match (m : Nat) (x : Cube m) (h : degree m x+2 ≤ m) :
    zeta m (multiplicity m 0 false) x = zeta m (multiplicity m 0 true) x := by
  rw [all_intersection_counts m x h false,all_intersection_counts m x h true]

theorem multiplicity_nonnegative (n r : Nat) (b : Bool) (x : Cube n) : 0 ≤ multiplicity n r b x := by
  induction n generalizing r b with
  | zero => cases b <;> simp [multiplicity]
  | succ n ih => rcases x with ⟨c,x⟩; cases c <;> simp [multiplicity,ih]

theorem no_unused_sources (n : Nat) (b : Bool) : multiplicity n 0 b (empty n) = 0 := by
  induction n with
  | zero => cases b <;> rfl
  | succ n ih => simpa [empty,multiplicity] using ih

def fullParity : Nat → Bool
  | 0 => false
  | n+1 => !(fullParity n)

theorem full_multiplicity (n r : Nat) :
    multiplicity n r (fullParity n) (full n) = (r+n : Nat) ∧
    multiplicity n r (!(fullParity n)) (full n) = 0 := by
  induction n generalizing r with
  | zero => simp [fullParity,multiplicity,full]
  | succ n ih =>
    simp only [fullParity,full,multiplicity,if_true,Bool.not_not]
    have h := ih (r+1)
    constructor
    · rw [h.1]
      congr 1
      omega
    · exact h.2

theorem degree_full (n : Nat) : degree n (full n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [degree,full,ih,Nat.add_comm]

theorem degree_eq_full (n : Nat) (x : Cube n) : degree n x = n ↔ x = full n := by
  induction n with
  | zero => cases x; simp [degree,full]
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b
    · constructor
      · intro h
        have hd := degree_le n x
        simp [degree] at h
        omega
      · intro h
        have hh := congrArg Prod.fst h
        cases hh
    · constructor
      · intro h
        have hd : degree n x = n := by simp [degree] at h; omega
        have he := (ih x).1 hd
        cases he
        rfl
      · intro h
        cases h
        exact degree_full (n+1)

/-- System B has no positive-multiplicity pattern read by all m studies. -/
theorem opposite_parity_max_read (m : Nat) (x : Cube m)
    (hx : multiplicity m 0 (!(fullParity m)) x ≠ 0) : degree m x < m := by
  have hd := degree_le m x
  have hn : degree m x ≠ m := by
    intro h
    have he := (degree_eq_full m x).1 h
    subst x
    exact hx (full_multiplicity m 0).2
  omega

theorem zeta_full (n : Nat) (f : Cube n → Int) : zeta n f (full n) = f (full n) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (fun y => f (true,y))

theorem degree_empty (n : Nat) : degree n (empty n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [degree,empty] using ih

theorem union_count (m : Nat) (hm : 2 ≤ m) (b : Bool) :
    zeta m (multiplicity m 0 b) (empty m) = (m*2^(m-2) : Nat) := by
  have h := all_intersection_counts m (empty m) (by simpa [degree_empty] using hm) b
  simpa [degree_empty] using h

theorem full_intersections (m : Nat) :
    zeta m (multiplicity m 0 (fullParity m)) (full m) = (m : Int) ∧
    zeta m (multiplicity m 0 (!(fullParity m))) (full m) = 0 := by
  simp only [zeta_full]
  simpa using full_multiplicity m 0

theorem opposite_max_attained (n : Nat) :
    multiplicity (n+1) 0 (!(fullParity (n+1))) (false,full n) = (n : Int) ∧
    degree (n+1) (false,full n) = n := by
  constructor
  · simpa [multiplicity,fullParity] using (full_multiplicity n 0).1
  · simp [degree,degree_full]

def allIncluded : (n : Nat) → Cube n → Int
  | 0, _ => 1
  | n+1, (b,x) => if b then allIncluded n x else 0

def oneMissing : (n : Nat) → Cube n → Int
  | 0, _ => 0
  | n+1, (b,x) => if b then oneMissing n x else allIncluded n x

theorem zeta_allIncluded (n : Nat) (x : Cube n) : zeta n (allIncluded n) x = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b <;> simpa [zeta,allIncluded] using ih x

theorem zeta_oneMissing (n : Nat) (x : Cube n) :
    zeta n (oneMissing n) x = (n : Int) - (degree n x : Int) := by
  induction n with
  | zero => simp [zeta,oneMissing,degree]
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b
    · change zeta n (fun y => allIncluded n y+oneMissing n y) x = _
      rw [zeta_add,zeta_allIncluded,ih]
      simp [degree]
      omega
    · change zeta n (oneMissing n) x = _
      rw [ih]
      simp [degree]
      omega

theorem allIncluded_eq_one (n : Nat) (x : Cube n) : allIncluded n x = 1 ↔ x = full n := by
  induction n with
  | zero => cases x; simp [allIncluded,full]
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b
    · constructor
      · intro h; simp [allIncluded] at h
      · intro h; have hh := congrArg Prod.fst h; cases hh
    · constructor
      · intro h
        have he := (ih x).1 h
        cases he
        rfl
      · intro h
        have he := congrArg Prod.snd h
        exact (ih x).2 he

theorem oneMissing_binary (n : Nat) (x : Cube n) : oneMissing n x = 0 ∨ oneMissing n x = 1 := by
  have hfull : ∀ n, ∀ x : Cube n, allIncluded n x = 0 ∨ allIncluded n x = 1 := by
    intro n
    induction n with
    | zero => intro x; exact Or.inr rfl
    | succ n ih => intro ⟨b,x⟩; cases b; exact Or.inl rfl; exact ih x
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih => rcases x with ⟨b,x⟩; cases b; exact hfull n x; exact ih x

theorem oneMissing_multiplicity (n r : Nat) (x : Cube n) (hx : oneMissing n x = 1) :
    multiplicity n r (!(fullParity n)) x = (r+n-1 : Nat) := by
  induction n generalizing r with
  | zero => simp [oneMissing] at hx
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b
    · have he : x = full n := (allIncluded_eq_one n x).1 hx
      subst x
      simpa [multiplicity,fullParity] using (full_multiplicity n r).1
    · change multiplicity n (r+1) (!(!(fullParity (n+1)))) x = _
      simp only [fullParity,Bool.not_not]
      rw [ih (r+1) x hx]
      congr 1
      omega

theorem zeta_scale (n : Nat) (c : Int) (f : Cube n → Int) (x : Cube n) :
    zeta n (fun y => c*f y) x = c*zeta n f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b
    · change zeta n (fun y => c*f (false,y)+c*f (true,y)) x = _
      simp only [← Int.mul_add]
      exact ih (fun y => f (false,y)+f (true,y)) x
    · exact ih (fun y => f (true,y)) x

/-- The number of source copies with one missing study that lie in a query.
For a singleton query this equals (m-1)^2, the balancing denominator. -/
theorem balancing_source_count (m : Nat) (x : Cube m) :
    zeta m (fun y => (m-1 : Nat)*oneMissing m y) x =
      (m-1 : Nat)*((m : Int)-(degree m x : Int)) := by
  rw [zeta_scale,zeta_oneMissing]

theorem oneMissing_degree (n : Nat) (x : Cube n) (hx : oneMissing n x = 1) :
    degree n x + 1 = n := by
  induction n with
  | zero => simp [oneMissing] at hx
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b
    · have he := (allIncluded_eq_one n x).1 hx
      subst x
      simp [degree,degree_full]
    · have hd := ih x hx
      simp only [degree,if_true]
      omega

/-- The weighted top-layer indicator counts actual source copies in system B. -/
theorem actual_balancing_source_count (m : Nat) (x : Cube m) :
    zeta m (fun y => multiplicity m 0 (!(fullParity m)) y * oneMissing m y) x =
      (m-1 : Nat)*((m : Int)-(degree m x : Int)) := by
  have he : (fun y => multiplicity m 0 (!(fullParity m)) y * oneMissing m y) =
      (fun y => (m-1 : Nat)*oneMissing m y) := by
    funext y
    rcases oneMissing_binary m y with hy | hy
    · simp [hy]
    · rw [oneMissing_multiplicity m 0 y hy]
      simp
  rw [he,balancing_source_count]

theorem singleton_balancing_count (m : Nat) (x : Cube m) (hx : degree m x = 1) :
    zeta m (fun y => multiplicity m 0 (!(fullParity m)) y * oneMissing m y) x =
      (m-1 : Nat)*(m-1 : Nat) := by
  rw [actual_balancing_source_count,hx]
  have hm : 1 ≤ m := by have := degree_le m x; omega
  have hc : ((m-1 : Nat) : Int) = (m : Int)-1 := by omega
  rw [hc]
  rfl

end ParityIncidence
