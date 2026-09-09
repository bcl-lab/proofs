import ContinuousVille

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace RepeatedEvidenceProbability

/-- The non-strict threshold form displayed in the manuscript. Supremum
attainment is not required. -/
theorem MonitoringModel.ville_closed_tail {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) (u : ℝ) (hu : 0 < u) :
    model.μ {ω | ENNReal.ofReal u ≤ model.maximum i ω} ≤ ENNReal.ofReal (1/u) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : (0:ℝ) < ε := by exact_mod_cast hε
  let r : ℝ := 1/(1/u+(ε:ℝ))
  have hd : 0 < 1/u+(ε:ℝ) := add_pos (one_div_pos.mpr hu) hεr
  have hr : 0 < r := one_div_pos.mpr hd
  have hru : r < u := by
    apply (div_lt_iff₀ hd).mpr
    have he : u*(1/u+(ε:ℝ)) = 1+u*(ε:ℝ) := by field_simp; ring
    rw [he]
    linarith [mul_pos hu hεr]
  have hsub : {ω | ENNReal.ofReal u ≤ model.maximum i ω} ⊆
      {ω | ENNReal.ofReal r < model.maximum i ω} := by
    intro ω hω
    exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr.le).mpr hru).trans_le hω
  have hv := (measure_mono hsub).trans (model.ville_tail i r hr)
  have he : 1/r = 1/u+(ε:ℝ) := by simp [r]
  rw [he,ENNReal.ofReal_add (one_div_pos.mpr hu).le hεr.le,ENNReal.ofReal_coe_nnreal] at hv
  exact hv

end RepeatedEvidenceProbability
