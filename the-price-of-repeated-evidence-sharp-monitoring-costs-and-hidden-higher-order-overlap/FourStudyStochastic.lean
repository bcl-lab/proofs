import CappedCost

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem four_study_A_shared_source :
    ∀ i : Fin 4, RepeatedEvidence.uses RepeatedEvidence.maskA (12 : Fin 16) i := by
  decide

/-- The explicit 16-source system A has infinite universal monitoring cost
at the paper's study power 0.3. -/
theorem four_study_A_universal_cost_infinite :
    universalCost (RepeatedEvidence.uses RepeatedEvidence.maskA)
      (fun _ : Fin 4 => (3/10 : ℝ)) = ∞ := by
  apply universalCost_infinite_of_source_load _ _ (12 : Fin 16)
  change 1 ≤ ∑ i : Fin 4, if RepeatedEvidence.uses RepeatedEvidence.maskA (12 : Fin 16) i
    then (3/10 : ℝ) else 0
  simp only [if_pos (four_study_A_shared_source _)]
  norm_num

/-- The claimed system-A ceiling cost is identified with its actual universal
stochastic functional, rather than only checked as a closed expression. -/
theorem four_study_A_exact_capped_cost (H : ℝ) (hH : 1 ≤ H) :
    universalCappedCost (RepeatedEvidence.uses RepeatedEvidence.maskA) H
      (fun _ : Fin 4 => (3/10 : ℝ)) = ENNReal.ofReal (RepeatedEvidence.capCostA H) := by
  have h := universalCappedCost_common_source (RepeatedEvidence.uses RepeatedEvidence.maskA)
    (fun _ : Fin 4 => (3/10 : ℝ)) (by intro _; norm_num) (12 : Fin 16)
    four_study_A_shared_source H hH (by norm_num)
  norm_num at h
  simpa [RepeatedEvidence.capMoment_A_formula] using h

end RepeatedEvidenceProbability
