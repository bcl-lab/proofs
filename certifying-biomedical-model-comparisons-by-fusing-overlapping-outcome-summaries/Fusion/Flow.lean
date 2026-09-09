import Fusion.Basic

namespace Fusion
open Finset

/-- Integer record variables on unit-capacity arcs are binary. -/
theorem integer_unit_capacity (x : ℤ) :
    (0 ≤ x ∧ x ≤ 1) ↔ (x = 0 ∨ x = 1) := by omega

/-- Grouped sums count every record once, including parallel record edges. -/
theorem sum_group_counts {n h : ℕ} (g : Fin n → Fin h) (y : Fin n → ℤ) :
    (∑ b, ∑ i ∈ univ.filter (fun i => g i = b), y i) = ∑ i, y i := by
  exact sum_fiberwise univ g y

structure CountData (n h k : ℕ) where
  gA : Fin n → Fin h
  gB : Fin n → Fin k
  lowerA : Fin h → ℤ
  upperA : Fin h → ℤ
  lowerB : Fin k → ℤ
  upperB : Fin k → ℤ
  total : ℤ
  reviewed : Finset (Fin n)
  outcome : Fin n → ℤ

def groupCount {n h : ℕ} (g : Fin n → Fin h) (y : Fin n → ℤ) (b : Fin h) : ℤ :=
  ∑ i ∈ univ.filter (fun i => g i = b), y i

def CountFeasible {n h k : ℕ} (d : CountData n h k) (y : Fin n → ℤ) : Prop :=
  (∀ i, y i = 0 ∨ y i = 1) ∧
  (∑ i, y i) = d.total ∧
  (∀ b, d.lowerA b ≤ groupCount d.gA y b ∧ groupCount d.gA y b ≤ d.upperA b) ∧
  (∀ b, d.lowerB b ≤ groupCount d.gB y b ∧ groupCount d.gB y b ≤ d.upperB b) ∧
  (∀ i ∈ d.reviewed, y i = d.outcome i)

/-- Explicit integral flow constraints for source to A, record, and B to sink arcs. -/
def FlowFeasible {n h k : ℕ} (d : CountData n h k)
    (x : Fin n → ℤ) (s : Fin h → ℤ) (t : Fin k → ℤ) : Prop :=
  (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
  (∀ b, s b = groupCount d.gA x b) ∧
  (∀ b, t b = groupCount d.gB x b) ∧
  (∑ b, s b) = d.total ∧ (∑ b, t b) = d.total ∧
  (∀ b, d.lowerA b ≤ s b ∧ s b ≤ d.upperA b) ∧
  (∀ b, d.lowerB b ≤ t b ∧ t b ≤ d.upperB b) ∧
  (∀ i ∈ d.reviewed, x i = d.outcome i)

/-- Full integer-flow and binary-completion correspondence for two partitions.
    This theorem does not assert integrality of a real linear-program optimum. -/
theorem count_flow_correspondence {n h k : ℕ} (d : CountData n h k) (y : Fin n → ℤ) :
    CountFeasible d y ↔ ∃ s t, FlowFeasible d y s t := by
  constructor
  · rintro ⟨hy,ht,ha,hb,ho⟩
    refine ⟨groupCount d.gA y,groupCount d.gB y,?_,?_,?_,?_,?_,ha,hb,ho⟩
    · intro i; exact (integer_unit_capacity _).mpr (hy i)
    · intro b; rfl
    · intro b; rfl
    · exact (sum_group_counts d.gA y).trans ht
    · exact (sum_group_counts d.gB y).trans ht
  · rintro ⟨s,t,hx,hs,ht,hsum,_,ha,hb,ho⟩
    have hse : s = groupCount d.gA y := funext hs
    have hte : t = groupCount d.gB y := funext ht
    subst s; subst t
    refine ⟨fun i => (integer_unit_capacity _).mp (hx i),?_,ha,hb,ho⟩
    exact (sum_group_counts d.gA y).symm.trans hsum

/-- Minimization over integral flows is exactly minimization over completions. -/
theorem integral_optimizer_transfer {n h k : ℕ} (d : CountData n h k)
    (cost : (Fin n → ℤ) → ℝ) (y : Fin n → ℤ)
    (hy : CountFeasible d y) :
    (∀ z, CountFeasible d z → cost y ≤ cost z) ↔
    (∀ z s t, FlowFeasible d z s t → cost y ≤ cost z) := by
  constructor
  · intro hmin z s t hz
    exact hmin z ((count_flow_correspondence d z).mpr ⟨s,t,hz⟩)
  · intro hmin z hz
    obtain ⟨s,t,hst⟩ := (count_flow_correspondence d z).mp hz
    exact hmin z s t hst

/-- Complementation is an involution on every binary record. -/
theorem complement_binary (x : ℤ) (hx : x=0 ∨ x=1) :
    (1-x=0 ∨ 1-x=1) ∧ 1-(1-x)=x := by omega

/-- Signed conservation becomes a positive-count equation by complementing
    the negatively signed record variables. -/
theorem signed_count_conversion {n : ℕ} (neg : Fin n → Bool) (x : Fin n → ℤ) :
    (∑ i, if neg i then 1-x i else x i) =
    (∑ i, if neg i then -x i else x i) +
    ∑ i, if neg i then (1:ℤ) else 0 := by
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  cases h : neg i <;> simp [h] <;> omega

end Fusion
