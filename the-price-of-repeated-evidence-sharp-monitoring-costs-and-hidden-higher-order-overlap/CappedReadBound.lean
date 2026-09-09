import FinnerMonitoring
import FourStudyStochastic
import RepeatedEvidenceNumerics

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

/-- Corollary 3.1's system-B bound holds for every incidence pattern with
source read count at most d. It bounds the actual universal capped cost. -/
theorem universalCappedCost_le_read_bound {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (H a d : ℝ) (hH : 1 ≤ H)
    (ha : 0 < a) (hd : 0 < d)
    (hread : ∀ v, (∑ i, if A v i then (1:ℝ) else 0) ≤ d) :
    universalCappedCost A H (fun _ => a) ≤
      ENNReal.ofReal ((RepeatedEvidence.capMoment H (d*a)) ^ ((Fintype.card I:ℝ)/d)) := by
  have hfeas : ∀ v, (∑ i, if A v i then 1/d else 0) ≤ 1 := by
    intro v
    have he : (∑ i, if A v i then 1/d else 0) =
        (∑ i, if A v i then (1:ℝ) else 0)/d := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [he]
    exact (div_le_one hd).2 (hread v)
  have h := universalCappedCost_le_finner A H hH (fun _ => a) (fun _ => 1/d)
    (fun _ => ha) (fun _ => one_div_pos.mpr hd) hfeas
  have he : a / (1/d) = d*a := by field_simp; ring
  dsimp only at h
  rw [he] at h
  have hC : 0 < RepeatedEvidence.capMoment H (d*a) :=
    zero_lt_one.trans_le (capMoment_ge_one H (d*a) hH (mul_pos hd ha))
  simpa only [ENNReal.ofReal_rpow_of_pos hC,
    ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.rpow_pos_of_pos hC _).le),
    ← Real.rpow_sum_of_pos hC, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one_div] using h

theorem four_study_B_read_sum (v : Fin 16) :
    (∑ i : Fin 4, if RepeatedEvidence.uses RepeatedEvidence.maskB v i
      then (1:ℝ) else 0) ≤ 3 := by
  have h := RepeatedEvidence.four_study_maximum_reads.2.2.1 v
  simp only [RepeatedEvidence.readCount] at h
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast h

/-- The missing stochastic interpretation of the displayed system-B bound. -/
theorem four_study_B_capped_cost_bound (H : ℝ) (hH : 1 ≤ H) :
    universalCappedCost (RepeatedEvidence.uses RepeatedEvidence.maskB) H
      (fun _ : Fin 4 => (3/10:ℝ)) ≤ ENNReal.ofReal (RepeatedEvidence.capBoundB H) := by
  have h := universalCappedCost_le_read_bound (RepeatedEvidence.uses RepeatedEvidence.maskB)
    H (3/10) 3 hH (by norm_num) (by norm_num) four_study_B_read_sum
  norm_num only [show (3:ℝ)*(3/10) = 9/10 by norm_num, Fintype.card_fin] at h
  simpa only [RepeatedEvidence.capMoment_B_formula, RepeatedEvidence.capBoundB] using h

/-- The explicit system B is finite, while the earlier system-A theorem
proves divergence with exactly the same pairwise overlap summaries. -/
theorem four_study_B_universal_cost_finite :
    universalCost (RepeatedEvidence.uses RepeatedEvidence.maskB)
      (fun _ : Fin 4 => (3/10:ℝ)) ≠ ∞ := by
  apply (universalCost_finite_iff _ _ (fun _ => by norm_num)).2
  intro v
  have h := four_study_B_read_sum v
  have he : sourceLoad (RepeatedEvidence.uses RepeatedEvidence.maskB)
      (fun _ : Fin 4 => (3/10:ℝ)) v =
      (∑ i : Fin 4, if RepeatedEvidence.uses RepeatedEvidence.maskB v i
        then (1:ℝ) else 0) * (3/10) := by
    rw [Finset.sum_mul]
    unfold sourceLoad
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he]
  linarith

/-- The overlap penalty is a comparison of actual universal costs. -/
theorem four_study_capped_penalty_of_ratio (H r : ℝ) (hH : 1 ≤ H)
    (hr : 0 ≤ r) (hratio : r ≤ RepeatedEvidence.capCostA H / RepeatedEvidence.capBoundB H) :
    ENNReal.ofReal r * universalCappedCost (RepeatedEvidence.uses RepeatedEvidence.maskB) H
      (fun _ : Fin 4 => (3/10:ℝ)) ≤
    universalCappedCost (RepeatedEvidence.uses RepeatedEvidence.maskA) H
      (fun _ : Fin 4 => (3/10:ℝ)) := by
  have hbase : 0 < 10 - 9 * H ^ (-(1/10):ℝ) := by
    have h := capMoment_ge_one H (9/10) hH (by norm_num)
    rw [RepeatedEvidence.capMoment_B_formula] at h
    linarith
  have hB : 0 < RepeatedEvidence.capBoundB H := Real.rpow_pos_of_pos hbase _
  rw [four_study_A_exact_capped_cost H hH]
  calc
    _ ≤ ENNReal.ofReal r * ENNReal.ofReal (RepeatedEvidence.capBoundB H) :=
      mul_le_mul_left' (four_study_B_capped_cost_bound H hH) _
    _ = ENNReal.ofReal (r * RepeatedEvidence.capBoundB H) :=
      (ENNReal.ofReal_mul hr).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal ((le_div_iff₀ hB).1 hratio)

/-- The 5.88-fold penalty is now proved for the universal stochastic costs. -/
theorem four_study_universal_penalty_million :
    ENNReal.ofReal (588/100:ℝ) *
      universalCappedCost (RepeatedEvidence.uses RepeatedEvidence.maskB) 1000000
        (fun _ : Fin 4 => (3/10:ℝ)) ≤
      universalCappedCost (RepeatedEvidence.uses RepeatedEvidence.maskA) 1000000
        (fun _ : Fin 4 => (3/10:ℝ)) := by
  exact four_study_capped_penalty_of_ratio _ _ (by norm_num) (by norm_num)
    RepeatedEvidence.cap_ratio_million

/-- The 75.37-fold penalty is likewise connected to the universal functionals. -/
theorem four_study_universal_penalty_trillion :
    ENNReal.ofReal (7537/100:ℝ) *
      universalCappedCost (RepeatedEvidence.uses RepeatedEvidence.maskB) 1000000000000
        (fun _ : Fin 4 => (3/10:ℝ)) ≤
      universalCappedCost (RepeatedEvidence.uses RepeatedEvidence.maskA) 1000000000000
        (fun _ : Fin 4 => (3/10:ℝ)) := by
  exact four_study_capped_penalty_of_ratio _ _ (by norm_num) (by norm_num)
    RepeatedEvidence.cap_ratio_trillion

end RepeatedEvidenceProbability
