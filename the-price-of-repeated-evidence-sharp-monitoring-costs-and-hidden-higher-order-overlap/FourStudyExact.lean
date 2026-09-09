import WeightedGammaAttainment
import CappedReadBound

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem four_study_B_source_load (v : Fin 16) :
    sourceLoad (RepeatedEvidence.uses RepeatedEvidence.maskB) (fun _ : Fin 4 => (3/10:ℝ)) v =
      (RepeatedEvidence.readCount RepeatedEvidence.maskB v : ℝ) * (3/10) := by
  simp only [sourceLoad,RepeatedEvidence.readCount,← Finset.sum_filter,
    Finset.sum_const,nsmul_eq_mul]

/-- The exact finite value for the explicit system B, including its optimized
Finner cost. This uses the actual real-valued gamma certificate. -/
theorem four_study_B_exact_cost :
    universalCost (RepeatedEvidence.uses RepeatedEvidence.maskB) (fun _ : Fin 4 => (3/10:ℝ)) =
      ENNReal.ofReal ((10:ℝ)^(4/3:ℝ)) ∧
    optimizedFinnerCost (RepeatedEvidence.uses RepeatedEvidence.maskB)
      (fun _ : Fin 4 => (3/10:ℝ)) = ENNReal.ofReal ((10:ℝ)^(4/3:ℝ)) := by
  let A := RepeatedEvidence.uses RepeatedEvidence.maskB
  let q : Fin 16 → ℝ := fun v => RepeatedEvidence.certificateB v
  have hq : ∀ v, 0 ≤ q v := by
    intro v
    dsimp [q]
    exact_mod_cast RepeatedEvidence.four_study_B_certificate.1 v
  have hb : ∀ i : Fin 4, (∑ v, if A v i then q v else 0) = 1 := by
    intro i
    dsimp [A,q]
    have he (v : Fin 16) :
        (if RepeatedEvidence.uses RepeatedEvidence.maskB v i
          then (RepeatedEvidence.certificateB v:ℝ) else 0) =
        ((if RepeatedEvidence.uses RepeatedEvidence.maskB v i
          then RepeatedEvidence.certificateB v else 0 : ℚ):ℝ) := by
      split_ifs <;> norm_num
    simp_rw [he]
    exact_mod_cast RepeatedEvidence.four_study_B_certificate.2.1 i
  have hl : ∀ v, sourceLoad A (fun _ : Fin 4 => (3/10:ℝ)) v ≤ 9/10 := by
    intro v
    rw [four_study_B_source_load]
    have h : (RepeatedEvidence.readCount RepeatedEvidence.maskB v:ℝ) ≤ 3 := by
      exact_mod_cast RepeatedEvidence.four_study_maximum_reads.2.2.1 v
    linarith
  have hs : ∀ v, 0 < q v → sourceLoad A (fun _ : Fin 4 => (3/10:ℝ)) v = 9/10 := by
    intro v hv
    dsimp [q] at hv
    have hc : 0 < RepeatedEvidence.certificateB v := by exact_mod_cast hv
    rw [four_study_B_source_load,RepeatedEvidence.four_study_B_certificate.2.2 v hc]
    norm_num
  have h := weighted_gamma_attainment A (fun _ : Fin 4 => (3/10:ℝ)) q (9/10)
    (fun _ => by norm_num) hq (by norm_num) (by norm_num) hl hb hs
  have hv : (1-(9/10:ℝ))^(-((∑ _ : Fin 4, (3/10:ℝ))/(9/10))) = (10:ℝ)^(4/3:ℝ) := by
    norm_num
    rw [show (1/10:ℝ) = (10:ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num : (0:ℝ) ≤ 10),
      Real.rpow_neg (by norm_num : (0:ℝ) ≤ 10),inv_inv]
  simpa only [hv] using h

end RepeatedEvidenceProbability
