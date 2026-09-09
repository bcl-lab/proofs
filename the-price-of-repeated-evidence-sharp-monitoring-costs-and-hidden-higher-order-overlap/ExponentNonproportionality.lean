import AffineGammaObstruction

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace RepeatedEvidenceProbability

theorem exponential_gamma_nonproportional {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E G : Ω → ℝ)
    (hE : Measurable E) (hG : Measurable G) (k : ℝ) (hk : 1 < k)
    (hlawE : μ.map E = expMeasure 1) (hlawG : μ.map G = gammaShapeMeasure k)
    (α β A B : ℝ) (hα : 0 < α) (hβ : 0 < β) (hA : 0 < A) (hB : 0 < B) :
    ¬ (fun ω => Real.exp (α*E ω)/A) =ᵐ[μ] (fun ω => Real.exp (β*G ω)/B) := by
  intro he
  apply exponential_not_affine_gamma μ E G hE hG k hk hlawE hlawG
    (β/α) ((Real.log A-Real.log B)/α) (div_pos hβ hα)
  filter_upwards [he] with ω hω
  have hl := congrArg Real.log hω
  rw [Real.log_div (Real.exp_pos _).ne' hA.ne',Real.log_div (Real.exp_pos _).ne' hB.ne',
    Real.log_exp,Real.log_exp] at hl
  rw [div_mul_eq_mul_div,← add_div]
  apply (eq_div_iff hα.ne').mpr
  nlinarith

end RepeatedEvidenceProbability
