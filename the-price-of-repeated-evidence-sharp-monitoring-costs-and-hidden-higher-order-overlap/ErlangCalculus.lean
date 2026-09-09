import RepeatedEvidenceCalculus
import Mathlib.Probability.Distributions.Gamma

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

namespace RepeatedEvidenceProbability

noncomputable def erlangPolynomial (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), t^j/(j.factorial:ℝ)

noncomputable def erlangDensity (n : ℕ) (t : ℝ) : ℝ := t^n*Real.exp (-t)/(n.factorial:ℝ)

theorem erlangPolynomial_zero (n : ℕ) : erlangPolynomial n 0 = 1 := by
  simp [erlangPolynomial,Finset.sum_range_succ']

theorem erlangPolynomial_succ (n : ℕ) (t : ℝ) :
    erlangPolynomial (n+1) t = erlangPolynomial n t+t^(n+1)/((n+1).factorial:ℝ) := by
  exact Finset.sum_range_succ _ _

theorem erlangPolynomial_pos (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : 0 < erlangPolynomial n t := by
  apply Finset.sum_pos'
  · intro j _; positivity
  · refine ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ n),?_⟩
    norm_num

theorem erlangPolynomial_derivative (n : ℕ) (t : ℝ) :
    HasDerivAt (erlangPolynomial n) (erlangPolynomial n t-t^n/(n.factorial:ℝ)) t := by
  induction n with
  | zero =>
    have he : erlangPolynomial 0 = (fun _ : ℝ => 1) := by funext x; simp [erlangPolynomial]
    rw [he]
    simpa using hasDerivAt_const t (1:ℝ)
  | succ n ih =>
    have hf : ((n+1).factorial:ℝ) ≠ 0 := by positivity
    have hd := ((hasDerivAt_id t).pow (n+1)).div_const ((n+1).factorial:ℝ)
    have he : (erlangPolynomial (n+1)) =
        (fun x => erlangPolynomial n x+x^(n+1)/((n+1).factorial:ℝ)) := by
      funext x; exact erlangPolynomial_succ n x
    rw [he]
    convert ih.add hd using 1
    simp only [Nat.add_sub_cancel,erlangPolynomial_succ,id_eq,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp
    ring

theorem erlang_cdf_derivative (n : ℕ) (t : ℝ) :
    HasDerivAt (fun x => 1-Real.exp (-x)*erlangPolynomial n x) (erlangDensity n t) t := by
  have hd := (hasDerivAt_const t (1:ℝ)).sub
    (((hasDerivAt_id t).neg.exp).mul (erlangPolynomial_derivative n t))
  convert hd using 1
  dsimp [erlangDensity]
  ring

theorem gammaPDF_erlang (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    gammaPDFReal (n+1) 1 t = erlangDensity n t := by
  rw [gammaPDFReal,if_pos ht]
  have hg : Real.Gamma (n+1) = n.factorial := Real.Gamma_nat_eq_factorial n
  rw [hg]
  simp only [Real.one_rpow,add_sub_cancel_right,Real.rpow_natCast,one_mul,erlangDensity]
  ring

end RepeatedEvidenceProbability
