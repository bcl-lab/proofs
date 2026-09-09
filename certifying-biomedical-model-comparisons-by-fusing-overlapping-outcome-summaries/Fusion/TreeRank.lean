import Fusion.Tree
import Mathlib.Data.Fintype.BigOperators

namespace FusionTree
open Finset

def size : ℕ → ℕ
  | 0 => 2
  | k+1 => 2+2*size k

theorem size_formula (k : ℕ) : size k = 4*2^k-2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hp : 0 < (2:ℕ)^k := by positivity
    simp only [size,ih,pow_succ]
    omega

/-- Zero-based rank allocations. The two root ranks agree; child allocations
    exchange the model order, matching the alternating complementation. -/
def rank : (k : ℕ) → Bool → Edge k → ℕ
  | 0, flip, e => if e = flip then 0 else 1
  | k+1, _, .inl b => if b then 1 else 0
  | k+1, flip, .inr (b,e) => 2+(if b then size k else 0)+rank k (!flip) e

theorem rank_bound (k : ℕ) (flip : Bool) (e : Edge k) : rank k flip e < size k := by
  induction k generalizing flip with
  | zero => simp only [rank,size]; split_ifs <;> omega
  | succ k ih =>
    cases e with
    | inl b => cases b <;> simp only [rank,size,Bool.false_eq_true,if_false,if_true] <;> omega
    | inr be =>
      obtain ⟨b,e⟩ := be
      have h := ih (!flip) e
      cases b <;> simp only [rank,Bool.false_eq_true,if_false,if_true,size] <;> omega

theorem rank_injective (k : ℕ) (flip : Bool) : Function.Injective (rank k flip) := by
  induction k generalizing flip with
  | zero => intro e f h; cases flip <;> cases e <;> cases f <;> simp_all [rank]
  | succ k ih =>
    intro e f h
    cases e with
    | inl b =>
      cases f with
      | inl c => cases b <;> cases c <;> simp_all [rank]
      | inr ce =>
        obtain ⟨c,f⟩ := ce
        cases b <;> cases c <;> simp only [rank,Bool.false_eq_true,if_false,if_true] at h <;> omega
    | inr be =>
      obtain ⟨b,e⟩ := be
      cases f with
      | inl c => cases b <;> cases c <;> simp only [rank,Bool.false_eq_true,if_false,if_true] at h <;> omega
      | inr ce =>
        obtain ⟨c,f⟩ := ce
        have he := rank_bound k (!flip) e
        have hf := rank_bound k (!flip) f
        have hb : b=c := by
          cases b <;> cases c <;> simp only [rank,Bool.false_eq_true,if_false,if_true] at h <;> first | rfl | omega
        subst c
        have hr : rank k (!flip) e = rank k (!flip) f := by
          simp only [rank] at h; omega
        rw [ih (!flip) hr]

def rankFin (k : ℕ) (flip : Bool) (e : Edge k) : Fin (size k) :=
  ⟨rank k flip e,rank_bound k flip e⟩

theorem rank_bijective (k : ℕ) (flip : Bool) : Function.Bijective (rankFin k flip) := by
  have hi : Function.Injective (rankFin k flip) := by
    intro e f h
    exact rank_injective k flip (congrArg Fin.val h)
  refine ⟨hi,?_⟩
  by_contra hn
  have hc := Fintype.card_lt_of_injective_not_surjective (rankFin k flip) hi hn
  rw [edge_card,Fintype.card_fin,← size_formula] at hc
  omega

/-- Adding one converts these bijections to rank permutations of 1 through N. -/
noncomputable def rankPermutation (k : ℕ) (flip : Bool) : Edge k ≃ Fin (size k) :=
  Equiv.ofBijective (rankFin k flip) (rank_bijective k flip)

/-- Alternating complementation of flow coordinates by their origin depth. -/
def labels : (k : ℕ) → (Edge k → Bool) → Edge k → Bool
  | 0, x, e => x e
  | k+1, x, .inl b => x (.inl b)
  | k+1, x, .inr (b,e) => !(labels k (fun f => x (.inr (b,f))) e)

theorem labels_involution (k : ℕ) (x : Edge k → Bool) :
    labels k (labels k x) = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext e
    cases e with
    | inl b => rfl
    | inr be =>
      obtain ⟨b,e⟩ := be
      simp only [labels]
      have hn (j : ℕ) (z : Edge j → Bool) :
          labels j (fun f => !z f) = fun f => !(labels j z f) := by
        induction j with
        | zero => rfl
        | succ j hj =>
          funext f
          cases f with
          | inl c => rfl
          | inr cf => simp only [labels]; rw [congrFun (hj _) cf.2]
      rw [congrFun (hn k _) e,congrFun (ih _) e]
      simp

def coefficient (k : ℕ) (e : Edge k) : ℤ := (rank k false e : ℤ) - rank k true e

theorem root_coefficient (k : ℕ) (b : Bool) : coefficient (k+1) (.inl b) = 0 := by
  simp [coefficient,rank]

theorem child_coefficient (k : ℕ) (b : Bool) (e : Edge k) :
    coefficient (k+1) (.inr (b,e)) = -coefficient k e := by
  simp [coefficient,rank,Nat.cast_add]

/-- The coefficient sum is zero, so complementation introduces no offset. -/
theorem coefficient_sum (k : ℕ) : (∑ e, coefficient k e) = 0 := by
  induction k with
  | zero => simp [Edge,coefficient,rank,Fintype.sum_bool]
  | succ k ih =>
    simp [Edge,Fintype.sum_sum_type,Fintype.sum_prod_type,root_coefficient,child_coefficient,ih]

theorem bit_not (b : Bool) : bit (!b) = 1-bit b := by cases b <;> rfl

def target (k : ℕ) (x : Edge k → Bool) : ℤ :=
  ∑ e, coefficient k e * bit (labels k x e)

theorem target_step (k : ℕ) (x : Edge (k+1) → Bool) :
    target (k+1) x = target k (fun e => x (.inr (false,e))) +
      target k (fun e => x (.inr (true,e))) := by
  simp only [target,Edge,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
    root_coefficient,zero_mul,labels,child_coefficient,bit_not]
  simp_rw [mul_sub,mul_one,neg_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  simp [coefficient_sum]
  ring

theorem target_zero (k : ℕ) : target k (fun _ => false) = 0 := by
  induction k with
  | zero => simp [target,Edge,labels,bit]
  | succ k ih => rw [target_step,ih]; simp [ih]

/-- The all-depth, actual-rank contrast on complemented path labels is ±1. -/
theorem target_path (k : ℕ) (s : Leaf k × Bool) :
    target k (path k s) = if s.2 then 1 else -1 := by
  induction k with
  | zero => cases hs : s.2 <;> simp [target,Edge,Fintype.sum_bool,coefficient,rank,labels,path,bit,hs]
  | succ k ih =>
    rw [target_step]
    cases hb : s.1.1 <;> simp [path,hb,target_zero,ih]

theorem one_based_rank_difference (k : ℕ) (e : Edge k) :
    ((rank k false e : ℤ)+1)-((rank k true e : ℤ)+1) = coefficient k e := by
  simp [coefficient]

end FusionTree
