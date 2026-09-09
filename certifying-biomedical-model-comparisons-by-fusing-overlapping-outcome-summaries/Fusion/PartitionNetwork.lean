import Fusion.NetworkOpt
import Fusion.Flow
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators

namespace FusionPartition
open Finset Fusion FusionNetwork

abbrev Vertex (h k : ℕ) := Bool ⊕ (Fin h ⊕ Fin k)
abbrev Arc (n h k : ℕ) := Fin h ⊕ (Fin n ⊕ Fin k)

def src {n h k : ℕ} (d : CountData n h k) : Arc n h k → Vertex h k
  | .inl _ => .inl false
  | .inr (.inl i) => .inr (.inl (d.gA i))
  | .inr (.inr b) => .inr (.inr b)
def dst {n h k : ℕ} (d : CountData n h k) : Arc n h k → Vertex h k
  | .inl a => .inr (.inl a)
  | .inr (.inl i) => .inr (.inr (d.gB i))
  | .inr (.inr _) => .inl true

def lower {n h k : ℕ} (d : CountData n h k) : Arc n h k → ℤ
  | .inl a => d.lowerA a
  | .inr (.inl i) => if i ∈ d.reviewed then max 0 (d.outcome i) else 0
  | .inr (.inr b) => d.lowerB b
def upper {n h k : ℕ} (d : CountData n h k) : Arc n h k → ℤ
  | .inl a => d.upperA a
  | .inr (.inl i) => if i ∈ d.reviewed then min 1 (d.outcome i) else 1
  | .inr (.inr b) => d.upperB b
def supply {n h k : ℕ} (d : CountData n h k) : Vertex h k → ℤ
  | .inl false => d.total
  | .inl true => -d.total
  | .inr _ => 0

def realGroup {n h : ℕ} (g : Fin n → Fin h) (y : Fin n → ℝ) (a : Fin h) : ℝ :=
  ∑ i, if g i=a then y i else 0

theorem groups_sum {n h : ℕ} (g : Fin n → Fin h) (y : Fin n → ℝ) :
    (∑ a, realGroup g y a) = ∑ i, y i := by
  unfold realGroup
  rw [sum_comm]
  simp

theorem group_cast {n h : ℕ} (g : Fin n → Fin h) (y : Fin n → ℤ) (a : Fin h) :
    realGroup g (fun i => (y i : ℝ)) a = (groupCount g y a : ℝ) := by
  simp [realGroup,groupCount,sum_filter]

theorem balance_source {n h k : ℕ} (d : CountData n h k) (x : Arc n h k → ℝ) :
    balance (src d) (dst d) x (.inl false) = ∑ a, x (.inl a) := by
  simp [balance,incidence,src,dst,Fintype.sum_sum_type]
theorem balance_sink {n h k : ℕ} (d : CountData n h k) (x : Arc n h k → ℝ) :
    balance (src d) (dst d) x (.inl true) = -(∑ b, x (.inr (.inr b))) := by
  simp [balance,incidence,src,dst,Fintype.sum_sum_type]
theorem balance_A {n h k : ℕ} (d : CountData n h k) (x : Arc n h k → ℝ) (a : Fin h) :
    balance (src d) (dst d) x (.inr (.inl a)) =
      realGroup d.gA (fun i => x (.inr (.inl i))) a - x (.inl a) := by
  simp [balance,incidence,src,dst,Fintype.sum_sum_type,realGroup,ite_mul]
  ring
theorem balance_B {n h k : ℕ} (d : CountData n h k) (x : Arc n h k → ℝ) (b : Fin k) :
    balance (src d) (dst d) x (.inr (.inr b)) =
      x (.inr (.inr b)) - realGroup d.gB (fun i => x (.inr (.inl i))) b := by
  simp [balance,incidence,src,dst,Fintype.sum_sum_type,realGroup,ite_mul]
  ring

theorem record_bounds {n h k : ℕ} (d : CountData n h k) (i : Fin n) (x : ℝ) :
    ((lower d (.inr (.inl i)) : ℝ) ≤ x ∧ x ≤ (upper d (.inr (.inl i)) : ℝ)) ↔
      (0 ≤ x ∧ x ≤ 1) ∧ (i ∈ d.reviewed → x = (d.outcome i : ℝ)) := by
  by_cases hi : i ∈ d.reviewed
  · simp only [lower,upper,if_pos hi,Int.cast_max,Int.cast_min,Int.cast_zero,Int.cast_one,
      max_le_iff,le_min_iff,hi,true_implies,↓reduceIte]
    constructor
    · rintro ⟨⟨h0,ho⟩,h1,ho'⟩
      exact ⟨⟨h0,h1⟩,le_antisymm ho' ho⟩
    · rintro ⟨⟨h0,h1⟩,rfl⟩
      exact ⟨⟨h0,le_rfl⟩,h1,le_rfl⟩
  · simp [lower,upper,hi]

def RealCountFeasible {n h k : ℕ} (d : CountData n h k) (y : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ y i ∧ y i ≤ 1) ∧ (∑ i, y i) = (d.total : ℝ) ∧
  (∀ a, (d.lowerA a : ℝ) ≤ realGroup d.gA y a ∧ realGroup d.gA y a ≤ (d.upperA a : ℝ)) ∧
  (∀ b, (d.lowerB b : ℝ) ≤ realGroup d.gB y b ∧ realGroup d.gB y b ≤ (d.upperB b : ℝ)) ∧
  (∀ i ∈ d.reviewed, y i = (d.outcome i : ℝ))

def liftFlow {n h k : ℕ} (d : CountData n h k) (y : Fin n → ℝ) : Arc n h k → ℝ
  | .inl a => realGroup d.gA y a
  | .inr (.inl i) => y i
  | .inr (.inr b) => realGroup d.gB y b

theorem completion_lifts {n h k : ℕ} (d : CountData n h k) (y : Fin n → ℝ)
    (hy : RealCountFeasible d y) : RealFeasible (src d) (dst d) (lower d) (upper d) (supply d) (liftFlow d y) := by
  refine ⟨?_,?_⟩
  · intro e
    rcases e with a | i | b
    · exact hy.2.2.1 a
    · exact (record_bounds d i (y i)).mpr ⟨hy.1 i,hy.2.2.2.2 i⟩
    · exact hy.2.2.2.1 b
  · intro v
    rcases v with b | a | b
    · cases b
      · rw [balance_source]
        exact (groups_sum d.gA y).trans hy.2.1
      · rw [balance_sink]
        simpa only [liftFlow,groups_sum,hy.2.1,supply,Int.cast_neg] using
          congrArg Neg.neg hy.2.1
    · rw [balance_A]
      simp [liftFlow,supply]
    · rw [balance_B]
      simp [liftFlow,supply]

theorem feasible_projects {n h k : ℕ} (d : CountData n h k) (x : Arc n h k → ℝ)
    (hx : RealFeasible (src d) (dst d) (lower d) (upper d) (supply d) x) :
    RealCountFeasible d (fun i => x (.inr (.inl i))) := by
  have hA (a : Fin h) : realGroup d.gA (fun i => x (.inr (.inl i))) a = x (.inl a) := by
    have hh := hx.2 (.inr (.inl a))
    rw [balance_A] at hh
    simpa only [supply,Int.cast_zero,sub_eq_zero] using hh
  have hB (b : Fin k) : realGroup d.gB (fun i => x (.inr (.inl i))) b = x (.inr (.inr b)) := by
    have hh := hx.2 (.inr (.inr b))
    rw [balance_B] at hh
    exact (sub_eq_zero.mp (by simpa [supply] using hh)).symm
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; exact ((record_bounds d i _).mp (hx.1 (.inr (.inl i)))).1
  · have hh := hx.2 (.inl false)
    rw [balance_source] at hh
    rw [← groups_sum d.gA (fun i => x (.inr (.inl i)))]
    simpa only [hA] using hh
  · intro a; rw [hA]; exact hx.1 (.inl a)
  · intro b; rw [hB]; exact hx.1 (.inr (.inr b))
  · intro i hi; exact ((record_bounds d i _).mp (hx.1 (.inr (.inl i)))).2 hi

theorem integer_completion_iff {n h k : ℕ} (d : CountData n h k) (y : Fin n → ℤ) :
    CountFeasible d y ↔ RealCountFeasible d (fun i => (y i : ℝ)) := by
  constructor
  · rintro ⟨hy,hm,ha,hb,ho⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i; dsimp; exact_mod_cast (integer_unit_capacity (y i)).mpr (hy i)
    · dsimp at hm ⊢; exact_mod_cast hm
    · intro a; rw [group_cast]; exact_mod_cast ha a
    · intro b; rw [group_cast]; exact_mod_cast hb b
    · intro i hi; have hh := ho i hi; dsimp at hh ⊢; exact_mod_cast hh
  · rintro ⟨hy,hm,ha,hb,ho⟩
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro i; apply (integer_unit_capacity (y i)).mp; have hh := hy i; dsimp at hh; exact_mod_cast hh
    · dsimp at hm ⊢; exact_mod_cast hm
    · intro a; have hh := ha a; rw [group_cast] at hh; exact_mod_cast hh
    · intro b; have hh := hb b; rw [group_cast] at hh; exact_mod_cast hh
    · intro i hi; have hh := ho i hi; dsimp at hh ⊢; exact_mod_cast hh

def arcCost {n h k : ℕ} (a : Fin n → ℝ) : Arc n h k → ℝ
  | .inl _ => 0
  | .inr (.inl i) => a i
  | .inr (.inr _) => 0

theorem objective_eq {n h k : ℕ} (a : Fin n → ℝ) (x : Arc n h k → ℝ) :
    (∑ e, arcCost a e*x e) = ∑ i, a i*x (.inr (.inl i)) := by
  simp [arcCost,Fintype.sum_sum_type]

/-- Main Theorem 1 at the numerator level, including every real relaxed
    completion, with both endpoints attained by binary completions. -/
theorem two_partition_sharp {n h k : ℕ} (d : CountData n h k) (a : Fin n → ℝ)
    (hne : ∃ y, CountFeasible d y) :
    ∃ lo hi : Fin n → ℤ, CountFeasible d lo ∧ CountFeasible d hi ∧
      ∀ y, RealCountFeasible d y →
        (∑ i, a i*(lo i : ℝ)) ≤ (∑ i, a i*y i) ∧
        (∑ i, a i*y i) ≤ ∑ i, a i*(hi i : ℝ) := by
  have hflow : ∃ x, RealFeasible (src d) (dst d) (lower d) (upper d) (supply d) x := by
    obtain ⟨y,hy⟩ := hne
    exact ⟨liftFlow d (fun i => (y i : ℝ)),completion_lifts d _ ((integer_completion_iff d y).mp hy)⟩
  obtain ⟨lo,hi,hlo,hhi,he⟩ := integral_flow_extrema (src d) (dst d) (lower d) (upper d) (supply d) (arcCost a) hflow
  refine ⟨fun i => lo (.inr (.inl i)),fun i => hi (.inr (.inl i)),?_,?_,?_⟩
  · exact (integer_completion_iff d _).mpr (feasible_projects d _ hlo)
  · exact (integer_completion_iff d _).mpr (feasible_projects d _ hhi)
  · intro y hy
    have hh := he (liftFlow d y) (completion_lifts d y hy)
    simpa only [objective_eq,liftFlow] using hh

end FusionPartition
