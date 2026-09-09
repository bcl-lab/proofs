import RepeatedEvidence

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
open scoped BigOperators
open Finset
namespace RepeatedEvidence

noncomputable def finnerTerm (a b : ℝ) : ℝ := -(b * Real.log (1-a/b))
noncomputable def finnerFirst (a b : ℝ) : ℝ := -Real.log (1-a/b) - a/(b-a)

/-- Differentiation of the objective summand used in the optimization proof. -/
theorem finner_first_derivative (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    HasDerivAt (finnerTerm a) (finnerFirst a b) b := by
  have hb : b ≠ 0 := ne_of_gt (lt_trans ha hab)
  have hba : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hlog : 1-a/b ≠ 0 := by
    have hlt : a/b < 1 := (div_lt_one (lt_trans ha hab)).2 hab
    linarith
  have hd := (((hasDerivAt_const b (1:ℝ)).sub
    ((hasDerivAt_const b a).div (hasDerivAt_id b) hb)).log hlog)
  convert ((hasDerivAt_id b).mul hd).neg using 1
  unfold finnerFirst
  simp only [id_eq]
  field_simp [hb, hba, hlog]
  ring

/-- The exact second derivative in the manuscript. -/
theorem finner_second_derivative (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    HasDerivAt (finnerFirst a) (a^2/(b*(b-a)^2)) b := by
  have hb : b ≠ 0 := ne_of_gt (lt_trans ha hab)
  have hba : b-a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hlog : 1-a/b ≠ 0 := by
    have hlt : a/b < 1 := (div_lt_one (lt_trans ha hab)).2 hab
    linarith
  have hd := (((hasDerivAt_const b (1:ℝ)).sub
    ((hasDerivAt_const b a).div (hasDerivAt_id b) hb)).log hlog)
  have hquot := (hasDerivAt_const b a).div ((hasDerivAt_id b).sub_const a) hba
  convert hd.neg.sub hquot using 1
  simp only [id_eq]
  field_simp [hb, hba, hlog]
  ring

/-- The polynomial on the right side of the displayed hazard-derivative
identity is strictly positive for all k at least two and t positive. -/
theorem hazard_polynomial_positive (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t) :
    0 < ∑ j ∈ range n, ((n:ℝ)-j) * t^j / (j.factorial:ℝ) := by
  apply sum_pos'
  · intro j hj
    have hjn : (j:ℝ) < n := by exact_mod_cast mem_range.mp hj
    have hsub : 0 < (n:ℝ)-j := sub_pos.mpr hjn
    have hfact : (0:ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
    positivity
  · refine ⟨0, mem_range.mpr hn, ?_⟩
    have hn' : (0:ℝ) < n := by exact_mod_cast hn
    simpa using hn'

end RepeatedEvidence
