import Fusion.LaminarNetwork
import Mathlib.Data.Fintype.BigOperators

namespace FusionHierarchy
open Finset FusionLaminar FusionNetwork
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

structure Data (ι : Type*) where
  A : Finset (Finset ι)
  B : Finset (Finset ι)
  lowerA : Finset ι → ℤ
  upperA : Finset ι → ℤ
  lowerB : Finset ι → ℤ
  upperB : Finset ι → ℤ
  total : ℤ
  reviewed : Finset ι
  outcome : ι → ℤ

abbrev Vertex (ι : Type*) := Option (Finset ι) ⊕ Option (Finset ι)
abbrev Arc (ι : Type*) := Finset ι ⊕ (ι ⊕ Finset ι)

noncomputable def source (d : Data ι) : Arc ι → Vertex ι
  | .inl C => .inl (parent d.A C)
  | .inr (.inl i) => .inl (some {i})
  | .inr (.inr C) => .inr (some C)
noncomputable def destination (d : Data ι) : Arc ι → Vertex ι
  | .inl C => .inl (some C)
  | .inr (.inl i) => .inr (some {i})
  | .inr (.inr C) => .inr (parent d.B C)

def supplies (d : Data ι) : Vertex ι → ℤ
  | .inl none => d.total
  | .inr none => -d.total
  | _ => 0

noncomputable def treeCap (F : Finset (Finset ι)) (C : Finset ι) : ℤ := by
  classical
  exact if C ∈ completed F then Fintype.card ι else 0
noncomputable def treeLower (F : Finset (Finset ι)) (lo : Finset ι → ℤ) (C : Finset ι) : ℤ :=
  max 0 (if C ∈ F then lo C else 0)
noncomputable def treeUpper (F : Finset (Finset ι)) (up : Finset ι → ℤ) (C : Finset ι) : ℤ :=
  min (treeCap F C) (if C ∈ F then up C else treeCap F C)

noncomputable def arcLower (d : Data ι) : Arc ι → ℤ
  | .inl C => treeLower d.A d.lowerA C
  | .inr (.inl i) => if i ∈ d.reviewed then max 0 (d.outcome i) else 0
  | .inr (.inr C) => treeLower d.B d.lowerB C
noncomputable def arcUpper (d : Data ι) : Arc ι → ℤ
  | .inl C => treeUpper d.A d.upperA C
  | .inr (.inl i) => if i ∈ d.reviewed then min 1 (d.outcome i) else 1
  | .inr (.inr C) => treeUpper d.B d.upperB C

theorem tree_bounds_iff (F : Finset (Finset ι)) (lo up : Finset ι → ℤ) (C : Finset ι) (q : ℝ) :
    ((treeLower F lo C : ℝ) ≤ q ∧ q ≤ (treeUpper F up C : ℝ)) ↔
      (0 ≤ q ∧ q ≤ (treeCap F C : ℝ)) ∧
      (C ∈ F → (lo C : ℝ) ≤ q ∧ q ≤ (up C : ℝ)) := by
  classical
  by_cases hc : C ∈ F
  · simp [treeLower,treeUpper,hc,Int.cast_max,Int.cast_min,max_le_iff,le_min_iff,
      and_assoc,and_left_comm,and_comm]
  · simp [treeLower,treeUpper,hc]

theorem record_bounds_iff (d : Data ι) (i : ι) (q : ℝ) :
    ((arcLower d (.inr (.inl i)) : ℝ) ≤ q ∧ q ≤ (arcUpper d (.inr (.inl i)) : ℝ)) ↔
      (0 ≤ q ∧ q ≤ 1) ∧ (i ∈ d.reviewed → q = (d.outcome i : ℝ)) := by
  by_cases hi : i ∈ d.reviewed
  · simp only [arcLower,arcUpper,if_pos hi,Int.cast_max,Int.cast_min,Int.cast_zero,Int.cast_one,
      max_le_iff,le_min_iff,hi,true_implies,↓reduceIte]
    constructor
    · rintro ⟨⟨h0,ho⟩,h1,ho'⟩
      exact ⟨⟨h0,h1⟩,le_antisymm ho' ho⟩
    · rintro ⟨⟨h0,h1⟩,rfl⟩
      exact ⟨⟨h0,le_rfl⟩,h1,le_rfl⟩
  · simp [arcLower,arcUpper,hi]

theorem balance_A_node (d : Data ι) (x : Arc ι → ℝ) (S : Finset ι) :
    balance (source d) (destination d) x (.inl (some S)) =
      treeOut d.A (fun C => x (.inl C)) S + leafTerm (fun i => x (.inr (.inl i))) S - x (.inl S) := by
  classical
  simp [balance,incidence,source,destination,Fintype.sum_sum_type,treeOut,leafTerm,
    sub_mul,sum_sub_distrib,ite_mul] <;> ring

theorem balance_B_node (d : Data ι) (x : Arc ι → ℝ) (S : Finset ι) :
    balance (source d) (destination d) x (.inr (some S)) =
      x (.inr (.inr S)) - treeOut d.B (fun C => x (.inr (.inr C))) S -
        leafTerm (fun i => x (.inr (.inl i))) S := by
  classical
  simp [balance,incidence,source,destination,Fintype.sum_sum_type,treeOut,leafTerm,
    sub_mul,sum_sub_distrib,ite_mul] <;> ring

theorem balance_rootA (d : Data ι) (x : Arc ι → ℝ) :
    balance (source d) (destination d) x (.inl none) = rootOut d.A (fun C => x (.inl C)) := by
  classical
  simp [balance,incidence,source,destination,Fintype.sum_sum_type,rootOut,ite_mul]

theorem balance_rootB (d : Data ι) (x : Arc ι → ℝ) :
    balance (source d) (destination d) x (.inr none) = -rootOut d.B (fun C => x (.inr (.inr C))) := by
  classical
  simp [balance,incidence,source,destination,Fintype.sum_sum_type,rootOut,ite_mul,
    sub_mul,sum_sub_distrib]

/-- Real relaxation of exactly the supplied two laminar count families. -/
def RealCounts (d : Data ι) (y : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (∑ i, y i) = (d.total : ℝ) ∧
  (∀ S ∈ d.A, (d.lowerA S : ℝ) ≤ (∑ i ∈ S, y i) ∧ (∑ i ∈ S, y i) ≤ (d.upperA S : ℝ)) ∧
  (∀ S ∈ d.B, (d.lowerB S : ℝ) ≤ (∑ i ∈ S, y i) ∧ (∑ i ∈ S, y i) ≤ (d.upperB S : ℝ)) ∧
  (∀ i ∈ d.reviewed, y i = (d.outcome i : ℝ))

def IntegerCounts (d : Data ι) (y : ι → ℤ) : Prop :=
  (∀ i, y i=0 ∨ y i=1) ∧ (∑ i, y i) = d.total ∧
  (∀ S ∈ d.A, d.lowerA S ≤ (∑ i ∈ S, y i) ∧ (∑ i ∈ S, y i) ≤ d.upperA S) ∧
  (∀ S ∈ d.B, d.lowerB S ≤ (∑ i ∈ S, y i) ∧ (∑ i ∈ S, y i) ≤ d.upperB S) ∧
  (∀ i ∈ d.reviewed, y i = d.outcome i)

noncomputable def networkLift (d : Data ι) (y : ι → ℝ) : Arc ι → ℝ
  | .inl C => treeLift d.A y C
  | .inr (.inl i) => y i
  | .inr (.inr C) => treeLift d.B y C

theorem treeLift_original (F : Finset (Finset ι)) (y : ι → ℝ) (S : Finset ι)
    (hS : S ∈ F) : treeLift F y S = ∑ i ∈ S, y i := by
  classical
  by_cases hs : S.Nonempty
  · simp [treeLift,completed_original F S hS hs]
  · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hs
    subst S
    simp [treeLift]

theorem treeLift_bounds (F : Finset (Finset ι)) (lo up : Finset ι → ℤ) (y : ι → ℝ)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hc : ∀ S ∈ F, (lo S : ℝ) ≤ (∑ i ∈ S, y i) ∧ (∑ i ∈ S, y i) ≤ (up S : ℝ)) :
    ∀ S, (treeLower F lo S : ℝ) ≤ treeLift F y S ∧ treeLift F y S ≤ (treeUpper F up S : ℝ) := by
  classical
  intro S
  apply (tree_bounds_iff F lo up S _).mpr
  constructor
  · by_cases hs : S ∈ completed F
    · simp only [treeLift,treeCap,if_pos hs,Int.cast_natCast]
      refine ⟨sum_nonneg (fun i _ => (hy i).1),?_⟩
      have hsum := sum_le_sum (fun i (_ : i ∈ S) => (hy i).2)
      have hcard := card_le_card (subset_univ S)
      have hcard' : (S.card : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
      simpa using le_trans hsum (by simpa using hcard')
    · simp [treeLift,treeCap,hs]
  · intro hs
    rw [treeLift_original F y S hs]
    exact hc S hs

theorem tree_zero_outside (F : Finset (Finset ι)) (lo up : Finset ι → ℤ) (q : Finset ι → ℝ)
    (hq : ∀ S, (treeLower F lo S : ℝ) ≤ q S ∧ q S ≤ (treeUpper F up S : ℝ)) :
    ∀ S, S ∉ completed F → q S = 0 := by
  classical
  intro S hs
  have hh := ((tree_bounds_iff F lo up S (q S)).mp (hq S)).1
  have hc : treeCap F S = 0 := by simp [treeCap,hs]
  rw [hc,Int.cast_zero] at hh
  exact le_antisymm hh.2 hh.1

theorem counts_lift (d : Data ι) (ha : Laminar d.A) (hb : Laminar d.B)
    (y : ι → ℝ) (hy : RealCounts d y) :
    RealFeasible (source d) (destination d) (arcLower d) (arcUpper d) (supplies d) (networkLift d y) := by
  classical
  refine ⟨?_,?_⟩
  · intro e
    rcases e with C | i | C
    · exact treeLift_bounds d.A d.lowerA d.upperA y hy.1 hy.2.2.1 C
    · exact (record_bounds_iff d i _).mpr ⟨hy.1 i,hy.2.2.2.2 i⟩
    · exact treeLift_bounds d.B d.lowerB d.upperB y hy.1 hy.2.2.2.1 C
  · intro v
    rcases v with S | S
    · cases S with
      | none =>
        rw [balance_rootA]
        change rootOut d.A (treeLift d.A y) = (d.total:ℝ)
        rw [rootOut_eq d.A (treeLift d.A y) (by intro S hs; simp [treeLift,hs])]
        simpa [treeLift,completed_root,supplies] using hy.2.1
      | some S =>
        rw [balance_A_node]
        have hh := treeLift_node d.A ha y S
        simp only [supplies,Int.cast_zero]
        change treeOut d.A (treeLift d.A y) S + leafTerm y S - treeLift d.A y S = 0
        linarith
    · cases S with
      | none =>
        rw [balance_rootB]
        change -rootOut d.B (treeLift d.B y) = ((-d.total:ℤ):ℝ)
        rw [rootOut_eq d.B (treeLift d.B y) (by intro S hs; simp [treeLift,hs])]
        simpa [treeLift,completed_root,supplies] using congrArg Neg.neg hy.2.1
      | some S =>
        rw [balance_B_node]
        have hh := treeLift_node d.B hb y S
        simp only [supplies,Int.cast_zero]
        change treeLift d.B y S - treeOut d.B (treeLift d.B y) S - leafTerm y S = 0
        linarith

/-- Every conserved real network flow projects to exactly the original
    count constraints, including empty counted sets and reviewed records. -/
theorem flow_projects (d : Data ι) (ha : Laminar d.A) (hb : Laminar d.B)
    (x : Arc ι → ℝ)
    (hx : RealFeasible (source d) (destination d) (arcLower d) (arcUpper d) (supplies d) x) :
    RealCounts d (fun i => x (.inr (.inl i))) := by
  classical
  let y : ι → ℝ := fun i => x (.inr (.inl i))
  let qA : Finset ι → ℝ := fun C => x (.inl C)
  let qB : Finset ι → ℝ := fun C => x (.inr (.inr C))
  have hAbounds (S : Finset ι) : (treeLower d.A d.lowerA S : ℝ) ≤ qA S ∧
      qA S ≤ (treeUpper d.A d.upperA S : ℝ) := hx.1 (.inl S)
  have hBbounds (S : Finset ι) : (treeLower d.B d.lowerB S : ℝ) ≤ qB S ∧
      qB S ≤ (treeUpper d.B d.upperB S : ℝ) := hx.1 (.inr (.inr S))
  have hAzero := tree_zero_outside d.A d.lowerA d.upperA qA hAbounds
  have hBzero := tree_zero_outside d.B d.lowerB d.upperB qB hBbounds
  have hAcons (S : Finset ι) : treeOut d.A qA S + leafTerm y S = qA S := by
    have hh := hx.2 (.inl (some S))
    rw [balance_A_node] at hh
    simp only [supplies,Int.cast_zero] at hh
    change treeOut d.A qA S + leafTerm y S - qA S = (0:ℝ) at hh
    linarith
  have hBcons (S : Finset ι) : treeOut d.B qB S + leafTerm y S = qB S := by
    have hh := hx.2 (.inr (some S))
    rw [balance_B_node] at hh
    simp only [supplies,Int.cast_zero] at hh
    change qB S - treeOut d.B qB S - leafTerm y S = (0:ℝ) at hh
    linarith
  have hA := node_determines_tree d.A ha qA y hAcons
  have hB := node_determines_tree d.B hb qB y hBcons
  have hAoriginal (S : Finset ι) (hS : S ∈ d.A) : qA S = ∑ i ∈ S, y i := by
    by_cases hs : S.Nonempty
    · exact hA S (completed_original d.A S hS hs)
    · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hs
      subst S
      have hn : (∅ : Finset ι) ∉ completed d.A := by
        intro hh; exact (completed_nonempty d.A ∅ hh).ne_empty rfl
      simpa using hAzero ∅ hn
  have hBoriginal (S : Finset ι) (hS : S ∈ d.B) : qB S = ∑ i ∈ S, y i := by
    by_cases hs : S.Nonempty
    · exact hB S (completed_original d.B S hS hs)
    · have he : S = ∅ := not_nonempty_iff_eq_empty.mp hs
      subst S
      have hn : (∅ : Finset ι) ∉ completed d.B := by
        intro hh; exact (completed_nonempty d.B ∅ hh).ne_empty rfl
      simpa using hBzero ∅ hn
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; exact ((record_bounds_iff d i _).mp (hx.1 (.inr (.inl i)))).1
  · have hh := hx.2 (.inl none)
    rw [balance_rootA] at hh
    change rootOut d.A qA = (d.total:ℝ) at hh
    rw [rootOut_eq d.A qA hAzero,hA univ (completed_root d.A)] at hh
    exact hh
  · intro S hS
    have hh := ((tree_bounds_iff d.A d.lowerA d.upperA S (qA S)).mp (hAbounds S)).2 hS
    simpa only [hAoriginal S hS] using hh
  · intro S hS
    have hh := ((tree_bounds_iff d.B d.lowerB d.upperB S (qB S)).mp (hBbounds S)).2 hS
    simpa only [hBoriginal S hS] using hh
  · intro i hi; exact ((record_bounds_iff d i _).mp (hx.1 (.inr (.inl i)))).2 hi

theorem integer_counts_iff (d : Data ι) (y : ι → ℤ) :
    IntegerCounts d y ↔ RealCounts d (fun i => (y i : ℝ)) := by
  constructor
  · rintro ⟨hy,hm,ha,hb,ho⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i; dsimp; exact_mod_cast (Fusion.integer_unit_capacity (y i)).mpr (hy i)
    · dsimp; exact_mod_cast hm
    · intro S hS; dsimp; exact_mod_cast ha S hS
    · intro S hS; dsimp; exact_mod_cast hb S hS
    · intro i hi; dsimp; exact_mod_cast ho i hi
  · rintro ⟨hy,hm,ha,hb,ho⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i; apply (Fusion.integer_unit_capacity (y i)).mp
      have hh := hy i; dsimp at hh; exact_mod_cast hh
    · dsimp at hm; exact_mod_cast hm
    · intro S hS; have hh := ha S hS; dsimp at hh; exact_mod_cast hh
    · intro S hS; have hh := hb S hS; dsimp at hh; exact_mod_cast hh
    · intro i hi; have hh := ho i hi; dsimp at hh; exact_mod_cast hh

def recordCost (a : ι → ℝ) : Arc ι → ℝ
  | .inl _ => 0
  | .inr (.inl i) => a i
  | .inr (.inr _) => 0

theorem record_objective (a : ι → ℝ) (x : Arc ι → ℝ) :
    (∑ e, recordCost a e*x e) = ∑ i, a i*x (.inr (.inl i)) := by
  simp [recordCost,Fintype.sum_sum_type]

/-- Main Theorem 2: for arbitrary laminar input families, both endpoints
    of the real relaxed count problem are attained by binary completions. -/
theorem two_laminar_sharp (d : Data ι) (ha : Laminar d.A) (hb : Laminar d.B)
    (a : ι → ℝ) (hne : ∃ y, IntegerCounts d y) :
    ∃ lo hi : ι → ℤ, IntegerCounts d lo ∧ IntegerCounts d hi ∧
      ∀ y, RealCounts d y →
        (∑ i, a i*(lo i : ℝ)) ≤ (∑ i, a i*y i) ∧
        (∑ i, a i*y i) ≤ ∑ i, a i*(hi i : ℝ) := by
  have hflow : ∃ x, RealFeasible (source d) (destination d) (arcLower d) (arcUpper d) (supplies d) x := by
    obtain ⟨y,hy⟩ := hne
    exact ⟨networkLift d (fun i => (y i : ℝ)),counts_lift d ha hb _ ((integer_counts_iff d y).mp hy)⟩
  obtain ⟨lo,hi,hlo,hhi,he⟩ := integral_flow_extrema (source d) (destination d) (arcLower d) (arcUpper d) (supplies d) (recordCost a) hflow
  refine ⟨fun i => lo (.inr (.inl i)),fun i => hi (.inr (.inl i)),?_,?_,?_⟩
  · exact (integer_counts_iff d _).mpr (flow_projects d ha hb _ hlo)
  · exact (integer_counts_iff d _).mpr (flow_projects d ha hb _ hhi)
  · intro y hy
    have hh := he (networkLift d y) (counts_lift d ha hb y hy)
    simpa only [record_objective,networkLift] using hh

end FusionHierarchy
