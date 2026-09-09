import RepeatedEvidence

set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset
namespace RepeatedEvidence

/-- Expectation on a finite sample space. Weights are probabilities when
nonnegative and summing to one; the comparison lemmas need only nonnegativity. -/
def finiteMean {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ) : ℝ := ∑ ω, p ω * X ω

/-- Any reported statistic dominated by a valid e-value retains its expectation
bound in a finite probability model, regardless of the reporting rule. -/
theorem finite_reporting_valid {Ω : Type*} [Fintype Ω]
    (p E R : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (hRE : ∀ ω, R ω ≤ E ω) (hE : finiteMean p E ≤ 1) : finiteMean p R ≤ 1 := by
  apply le_trans _ hE
  apply sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (hRE ω) (hp ω)

/-- Fixed weighted mixtures preserve the mean bound in a finite model. -/
theorem finite_mixture_valid {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : Ω → ℝ) (E : J → Ω → ℝ) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (hE : ∀ j, finiteMean p (E j) ≤ 1) :
    finiteMean p (fun ω => ∑ j, w j * E j ω) ≤ 1 := by
  have hid : finiteMean p (fun ω => ∑ j, w j * E j ω) =
      ∑ j, w j * finiteMean p (E j) := by
    unfold finiteMean
    simp_rw [mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro ω _
    ring
  rw [hid]
  calc
    ∑ j, w j * finiteMean p (E j) ≤ ∑ j, w j * 1 := by
      apply sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hE j) (hw j)
    _ = 1 := by simpa using hs

/-- The finite-model mean guarantee for a normalized nonnegative upper envelope. -/
theorem finite_normalized_valid {Ω : Type*} [Fintype Ω]
    (p X : Ω → ℝ) (K : ℝ) (hK : 0 < K) (hX : finiteMean p X ≤ K) :
    finiteMean p (fun ω => X ω/K) ≤ 1 := by
  have he : finiteMean p (fun ω => X ω/K) = finiteMean p X/K := by
    simp only [finiteMean, div_eq_mul_inv, mul_assoc, sum_mul]
  rw [he]
  exact (div_le_one hK).2 hX

/-- Exact finite counterexample: maximizing two individually valid e-values
after observing the outcome can double the null expectation. -/
theorem adaptive_maximum_counterexample :
    let p : Fin 2 → ℝ := fun _ => 1/2
    let e₁ : Fin 2 → ℝ := ![2,0]
    let e₂ : Fin 2 → ℝ := ![0,2]
    finiteMean p e₁ = 1 ∧ finiteMean p e₂ = 1 ∧
      finiteMean p (fun ω => max (e₁ ω) (e₂ ω)) = 2 := by
  norm_num [finiteMean, Fin.sum_univ_two]

end RepeatedEvidence
