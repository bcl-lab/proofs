import Std

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace OverlapReconstruction

/-- Binary coordinates specify an exact sharing pattern or an intersection query. -/
def Cube : Nat → Type
  | 0 => Unit
  | n+1 => Bool × Cube n

def full : (n : Nat) → Cube n
  | 0 => ()
  | n+1 => (true, full n)

def empty : (n : Nat) → Cube n
  | 0 => ()
  | n+1 => (false, empty n)

/-- Sum of exact-pattern multiplicities over supersets of an intersection query.
A false query coordinate permits both source-coordinate values. -/
def zeta : (n : Nat) → (Cube n → Int) → Cube n → Int
  | 0, f, x => f x
  | n+1, f, (b,x) =>
    if b then zeta n (fun y => f (true,y)) x
    else zeta n (fun y => f (false,y) + f (true,y)) x

/-- Boolean-lattice inversion, by subtraction along each coordinate. -/
def invert : (n : Nat) → (Cube n → Int) → Cube n → Int
  | 0, g, x => g x
  | n+1, g, (b,x) =>
    if b then invert n (fun y => g (true,y)) x
    else invert n (fun y => g (false,y)) x - invert n (fun y => g (true,y)) x

theorem invert_zeta (n : Nat) (f : Cube n → Int) (x : Cube n) :
    invert n (zeta n f) x = f x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b <;> simp [invert, zeta, ih]

theorem invert_zero (n : Nat) (x : Cube n) : invert n (fun _ => 0) x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rcases x with ⟨b,x⟩; cases b <;> simp [invert, ih]

theorem invert_sub (n : Nat) (f g : Cube n → Int) (x : Cube n) :
    invert n (fun y => f y-g y) x = invert n f x-invert n g x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases x with ⟨b,x⟩
    cases b <;> simp [invert, ih]
    omega

/-- When only the full-intersection entry can be nonzero, the empty-pattern
entry of its inversion vanishes exactly when that full entry vanishes. -/
theorem single_missing_intersection (n : Nat) (g : Cube n → Int)
    (hproper : ∀ x, x ≠ full n → g x = 0) :
    invert n g (empty n) = 0 ↔ g (full n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hf : (fun y : Cube n => g (false,y)) = fun _ => 0 := by
      funext y
      apply hproper
      intro h
      have hh := congrArg Prod.fst h
      cases hh
    have ht : ∀ y : Cube n, y ≠ full n → g (true,y) = 0 := by
      intro y hy
      apply hproper
      intro h
      exact hy (congrArg Prod.snd h)
    change (invert n (fun y => g (false,y)) (empty n) -
      invert n (fun y => g (true,y)) (empty n) = 0) ↔ g (true,full n) = 0
    rw [hf, invert_zero]
    simpa using ih (fun y => g (true,y)) ht

/-- All intersection counts identify every exact-pattern multiplicity. -/
theorem zeta_injective (n : Nat) (f g : Cube n → Int)
    (h : zeta n f = zeta n g) : f = g := by
  funext x
  calc
    f x = invert n (zeta n f) x := (invert_zeta n f x).symm
    _ = invert n (zeta n g) x := congrArg (fun q => invert n q x) h
    _ = g x := invert_zeta n g x

/-- The manuscript's optimal reconstruction corollary. Matching all proper
intersection queries, including the empty query (union count), and having no
source outside every study, forces matching exact sharing-pattern counts. -/
theorem proper_intersections_reconstruct (n : Nat) (f g : Cube n → Int)
    (hfempty : f (empty n) = 0) (hgempty : g (empty n) = 0)
    (hproper : ∀ x, x ≠ full n → zeta n f x = zeta n g x) : f = g := by
  let d : Cube n → Int := fun x => zeta n f x-zeta n g x
  have hd : ∀ x, x ≠ full n → d x = 0 := by
    intro x hx
    simp [d, hproper x hx]
  have hz : invert n d (empty n) = 0 := by
    dsimp [d]
    rw [invert_sub, invert_zeta, invert_zeta, hfempty, hgempty]
    rfl
  have hfull : d (full n) = 0 := (single_missing_intersection n d hd).1 hz
  apply zeta_injective
  funext x
  by_cases hx : x = full n
  · subst x
    exact Int.sub_eq_zero.mp hfull
  · exact hproper x hx

#print axioms invert_zeta
#print axioms invert_zero
#print axioms invert_sub
#print axioms single_missing_intersection
#print axioms zeta_injective
#print axioms proper_intersections_reconstruct
end OverlapReconstruction
