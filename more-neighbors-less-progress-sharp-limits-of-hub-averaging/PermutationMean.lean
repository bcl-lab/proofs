import RandomSweep
import Mathlib.Algebra.BigOperators.Field
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Perm

set_option maxHeartbeats 5000000
namespace HubAveraging
noncomputable section
open Finset

/-- Direct arithmetic mean over all permutations, with their actual sweeps. -/
def permutationLoss (n : ℕ) (h : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ e : Equiv.Perm (Fin n), sweepLoss h (List.ofFn (fun i => x (e i)))) / n.factorial

theorem perm_tail_sum (n : ℕ) (x : Fin (n+1) → ℝ) (p : Fin (n+1)) :
    (∑ i : Fin n, x (Equiv.swap 0 p i.succ)) = (∑ i, x i)-x p := by
  have he := Equiv.sum_comp (Equiv.swap 0 p) x
  rw [Fin.sum_univ_succ] at he
  simp only [Equiv.swap_apply_left] at he
  linarith

/-- Uniform permutations decompose into a uniform first leaf and a uniform
permutation of the remaining leaves. This uses a proved finite equivalence. -/
theorem permutationLoss_step (n : ℕ) (h : ℝ) (x : Fin (n+1) → ℝ) :
    permutationLoss (n+1) h x =
      (∑ p, ((h-x p)^2/2 + permutationLoss n ((h+x p)/2)
        (fun i => x (Equiv.swap 0 p i.succ)))) / (n+1) := by
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  have he := (Equiv.Perm.decomposeFin (n := n)).symm.sum_comp
    (fun e : Equiv.Perm (Fin (n+1)) => sweepLoss h (List.ofFn (fun i => x (e i))))
  unfold permutationLoss at ⊢
  rw [← he, Fintype.sum_prod_type]
  simp_rw [List.ofFn_succ, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, sweepLoss]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [sum_add_distrib, ← mul_sum, ← sum_div]
  field_simp
  ring

/-- Lemma 1's exact expectation for every degree, now for the literal uniform
distribution over all permutations rather than an assumed invariant form. -/
theorem uniform_permutation_loss (n : ℕ) (h : ℝ) (x : Fin n → ℝ) :
    permutationLoss n h x = localFormula n h (∑ i, x i) (∑ i, (x i)^2) := by
  induction n generalizing h with
  | zero => simp [permutationLoss, localFormula, r, sweepLoss]
  | succ n ih =>
    cases n with
    | zero =>
      rw [permutationLoss_step]
      simp [permutationLoss, localFormula, r, a, alpha, sweepLoss]
      ring
    | succ n =>
      rw [permutationLoss_step]
      simp_rw [ih, perm_tail_sum]
      have hq (p : Fin (n+1+1)) :
          (∑ i : Fin (n+1), (x (Equiv.swap 0 p i.succ))^2) = (∑ i, (x i)^2)-(x p)^2 :=
        perm_tail_sum (n+1) (fun i => (x i)^2) p
      simp_rw [hq]
      simpa using localFormula_average (n+1) (by omega) (univ : Finset (Fin (n+1+1)))
        (by simp) x h

end
end HubAveraging
