import Fusion.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Archimedean
import Mathlib.Logic.Relation

namespace FusionNetwork
open Finset
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def IsInt (x : ℝ) : Prop := ∃ z : ℤ, (z : ℝ) = x

theorem int_zero : IsInt 0 := ⟨0,Int.cast_zero⟩
theorem int_add {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x+y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a+b,Int.cast_add a b⟩
theorem int_sub {x y : ℝ} (hx : IsInt x) (hy : IsInt y) : IsInt (x-y) := by
  obtain ⟨a,rfl⟩ := hx; obtain ⟨b,rfl⟩ := hy
  exact ⟨a-b,Int.cast_sub a b⟩
theorem int_sum {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (h : ∀ i ∈ S, IsInt (x i)) : IsInt (∑ i ∈ S, x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using int_zero
  | @insert i S hi ih =>
    rw [sum_insert hi]
    exact int_add (h i (mem_insert_self _ _)) (ih (fun j hj => h j (mem_insert_of_mem hj)))

def incidence (src dst : E → V) (v : V) (e : E) : ℝ :=
  (if src e = v then 1 else 0) - (if dst e = v then 1 else 0)
def balance (src dst : E → V) (x : E → ℝ) (v : V) : ℝ :=
  ∑ e, incidence src dst v e * x e

theorem balance_zero (src dst : E → V) (v : V) : balance src dst (fun _ => 0) v = 0 := by
  simp [balance]
theorem balance_add (src dst : E → V) (x y : E → ℝ) (v : V) :
    balance src dst (fun e => x e+y e) v = balance src dst x v + balance src dst y v := by
  simp [balance,mul_add,sum_add_distrib]
theorem balance_sub (src dst : E → V) (x y : E → ℝ) (v : V) :
    balance src dst (fun e => x e-y e) v = balance src dst x v - balance src dst y v := by
  simp [balance,mul_sub,sum_sub_distrib]
theorem balance_scale (src dst : E → V) (x : E → ℝ) (t : ℝ) (v : V) :
    balance src dst (fun e => t*x e) v = t*balance src dst x v := by
  simp only [balance,mul_sum]
  apply sum_congr rfl; intro e he; ring

theorem balance_single (src dst : E → V) (e : E) (a : ℝ) (v : V) :
    balance src dst (Pi.single e a) v = incidence src dst v e * a := by
  classical
  simp [balance,Pi.single_apply]

def cutTerm (src dst : E → V) (S : Finset V) (x : E → ℝ) (e : E) : ℝ :=
  (if src e ∈ S then x e else 0) - (if dst e ∈ S then x e else 0)

theorem cut_balance (src dst : E → V) (S : Finset V) (x : E → ℝ) :
    (∑ v ∈ S, balance src dst x v) = ∑ e, cutTerm src dst S x e := by
  simp only [balance]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  simp [incidence,sub_mul,sum_sub_distrib,cutTerm,eq_comm]

theorem cutTerm_int (src dst : E → V) (S : Finset V) (x : E → ℝ) (e : E)
    (h : IsInt (x e)) : IsInt (cutTerm src dst S x e) := by
  unfold cutTerm
  apply int_sub
  · split <;> first | exact h | exact int_zero
  · split <;> first | exact h | exact int_zero

/-- Fractional edges other than a chosen edge can be traversed in either direction. -/
def Step (src dst : E → V) (x : E → ℝ) (e0 : E) (u v : V) : Prop :=
  ∃ e, e ≠ e0 ∧ ¬IsInt (x e) ∧
    ((src e = u ∧ dst e = v) ∨ (dst e = u ∧ src e = v))

/-- If all vertex balances are integers, any fractional edge has an alternate
    undirected fractional path between its endpoints. The cut proof also permits
    parallel edges and loops. -/
theorem fractional_connected (src dst : E → V) (x : E → ℝ)
    (hb : ∀ v, IsInt (balance src dst x v)) (e0 : E) (he0 : ¬IsInt (x e0)) :
    Relation.ReflTransGen (Step src dst x e0) (src e0) (dst e0) := by
  classical
  by_contra hn
  let S : Finset V := univ.filter (Relation.ReflTransGen (Step src dst x e0) (src e0))
  have hmem (v : V) : v ∈ S ↔ Relation.ReflTransGen (Step src dst x e0) (src e0) v := by
    simp [S]
  have hs : src e0 ∈ S := (hmem _).mpr .refl
  have hd : dst e0 ∉ S := fun h => hn ((hmem _).mp h)
  have hclosed (e : E) (he : e ≠ e0) (hf : ¬IsInt (x e)) : src e ∈ S ↔ dst e ∈ S := by
    constructor
    · intro h
      exact (hmem _).mpr (((hmem _).mp h).tail ⟨e,he,hf,Or.inl ⟨rfl,rfl⟩⟩)
    · intro h
      exact (hmem _).mpr (((hmem _).mp h).tail ⟨e,he,hf,Or.inr ⟨rfl,rfl⟩⟩)
  have hterms : ∀ e ∈ univ.erase e0, IsInt (cutTerm src dst S x e) := by
    intro e he
    by_cases hf : IsInt (x e)
    · exact cutTerm_int src dst S x e hf
    · have hc := hclosed e (mem_erase.mp he).1 hf
      have hz : cutTerm src dst S x e = 0 := by
        unfold cutTerm
        by_cases hm : src e ∈ S
        · simp [hm,hc.mp hm]
        · have hm' : dst e ∉ S := fun h => hm (hc.mpr h)
          simp [hm,hm']
      rw [hz]; exact int_zero
  have hcut : IsInt (∑ e, cutTerm src dst S x e) := by
    rw [← cut_balance]
    exact int_sum S _ (fun v _ => hb v)
  have hrest := int_sum (univ.erase e0) (cutTerm src dst S x) hterms
  have heq : (∑ e, cutTerm src dst S x e) -
      (∑ e ∈ univ.erase e0, cutTerm src dst S x e) = x e0 := by
    have hsum := sum_erase_add univ (cutTerm src dst S x) (mem_univ e0)
    have ht : cutTerm src dst S x e0 = x e0 := by simp [cutTerm,hs,hd]
    rw [ht] at hsum
    linarith
  exact he0 (heq ▸ int_sub hcut hrest)

/-- A fractional path determines a signed real transport vector without any
    simplicity requirement on the path. -/
theorem path_transport (src dst : E → V) (x : E → ℝ) (e0 : E)
    (a b : V) (hp : Relation.ReflTransGen (Step src dst x e0) a b) :
    ∃ d : E → ℝ, d e0 = 0 ∧ (∀ e, IsInt (x e) → d e = 0) ∧
      ∀ v, balance src dst d v = (if a=v then 1 else 0) - (if b=v then 1 else 0) := by
  induction hp with
  | refl =>
    refine ⟨fun _ => 0,rfl,fun _ _ => rfl,?_⟩
    intro v; simp [balance]
  | @tail b c hp step ih =>
    obtain ⟨d,hd0,hds,hdb⟩ := ih
    obtain ⟨e,he,hf,hends⟩ := step
    have hz : (Pi.single e (1:ℝ) : E → ℝ) e0 = 0 := by simp [Pi.single_apply,he,Ne.symm he]
    have hzi (i : E) (hi : IsInt (x i)) : (Pi.single e (1:ℝ) : E → ℝ) i = 0 := by
      have hne : i ≠ e := by intro hh; subst i; exact hf hi
      simp [Pi.single_apply,hne]
    rcases hends with hends | hends
    · refine ⟨fun i => d i + (Pi.single e (1:ℝ) : E → ℝ) i,by dsimp; rw [hd0,hz]; ring,?_,?_⟩
      · intro i hi; dsimp; rw [hds i hi,hzi i hi]; ring
      · intro v
        rw [balance_add,balance_single,hdb]
        unfold incidence
        rw [hends.1,hends.2]
        ring
    · refine ⟨fun i => d i - (Pi.single e (1:ℝ) : E → ℝ) i,by dsimp; rw [hd0,hz]; ring,?_,?_⟩
      · intro i hi; dsimp; rw [hds i hi,hzi i hi]; ring
      · intro v
        rw [balance_sub,balance_single,hdb]
        unfold incidence
        rw [hends.1,hends.2]
        ring

theorem fractional_circulation (src dst : E → V) (x : E → ℝ)
    (hb : ∀ v, IsInt (balance src dst x v)) (e0 : E) (he0 : ¬IsInt (x e0)) :
    ∃ d : E → ℝ, d e0 = 1 ∧ (∀ e, IsInt (x e) → d e = 0) ∧
      ∀ v, balance src dst d v = 0 := by
  obtain ⟨q,hq0,hqs,hqb⟩ := path_transport src dst x e0 (src e0) (dst e0)
    (fractional_connected src dst x hb e0 he0)
  refine ⟨fun e => (Pi.single e0 (1:ℝ) : E → ℝ) e - q e,?_,?_,?_⟩
  · simp [hq0]
  · intro e he
    have hne : e ≠ e0 := by intro hh; subst e; exact he0 he
    simp [Pi.single_apply,hne,hqs e he]
  · intro v
    rw [balance_sub,balance_single,hqb]
    simp [incidence]

/-- Choose a nonzero circulation direction with nonpositive linear cost. -/
theorem improving_direction (src dst : E → V) (x cost : E → ℝ)
    (hb : ∀ v, IsInt (balance src dst x v)) (hf : ∃ e, ¬IsInt (x e)) :
    ∃ d : E → ℝ, (∃ e, d e ≠ 0) ∧ (∀ e, IsInt (x e) → d e = 0) ∧
      (∀ v, balance src dst d v = 0) ∧ (∑ e, cost e*d e) ≤ 0 := by
  obtain ⟨e,he⟩ := hf
  obtain ⟨d,hde,hds,hdb⟩ := fractional_circulation src dst x hb e he
  by_cases hc : (∑ i, cost i*d i) ≤ 0
  · exact ⟨d,⟨e,by rw [hde]; norm_num⟩,hds,hdb,hc⟩
  · refine ⟨fun i => -1*d i,⟨e,by dsimp; rw [hde]; norm_num⟩,?_,?_,?_⟩
    · intro i hi; dsimp; rw [hds i hi]; ring
    · intro v; rw [balance_scale,hdb]; ring
    · have heq : (∑ i, cost i * (-1*d i)) = -(∑ i, cost i*d i) := by
        simp [mul_neg,mul_assoc]
      rw [heq]
      linarith

end FusionNetwork
