import GammaConstruction

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

/-- Generic source-compatible survival construction. All marginal laws are
checked inputs; the martingales, filtrations and maxima are then proved. -/
noncomputable def survivalModel {V I Ω : Type} [mΩ : MeasurableSpace Ω]
    (A : V → I → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sources : V → MeasurableSpace Ω) (hsub : ∀ v, sources v ≤ mΩ)
    (hind : iIndep sources μ) (Z : I → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hsource : ∀ i, Measurable[studyInformation A sources i] (Z i))
    (hlaw : ∀ i, μ.map (Z i) = expMeasure 1) : MonitoringModel A := {
  Ω := Ω
  μ := μ
  sources := sources
  sources_le := hsub
  independent := hind
  filtration := fun i => survivalFiltration (fun t : ℝ≥0 => {ω | (t:ℝ) < Z i ω})
    (fun s t h ω hω => lt_of_le_of_lt (show (s:ℝ) ≤ (t:ℝ) from h) hω)
  process := fun i t ω => exponentialSurvival t (Z i ω)
  valid := fun i => (exponential_law_survival_martingale μ (Z i) (hZ i) (hlaw i)).supermartingale
  nonnegative := fun _ _ _ => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  initial := fun i => (exponential_law_positive_ae μ (Z i) (hZ i) (hlaw i)).mono
    (fun ω hω => exponential_initial _ hω)
  right_continuous := fun _ _ t => exponential_survival_right_continuous _ t
  source_measurable := fun i _ => (measurable_const.indicator measurableSet_Ioi).comp (hsource i)
  maximum_measurable := fun i => exponential_extended_maximum_measurable.comp (hZ i)
}

theorem survivalModel_maximum {V I Ω : Type} [mΩ : MeasurableSpace Ω]
    (A : V → I → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sources : V → MeasurableSpace Ω) (hsub : ∀ v, sources v ≤ mΩ)
    (hind : iIndep sources μ) (Z : I → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hsource : ∀ i, Measurable[studyInformation A sources i] (Z i))
    (hlaw : ∀ i, μ.map (Z i) = expMeasure 1) (i : I) :
    ∀ᵐ ω ∂μ, (survivalModel A μ sources hsub hind Z hZ hsource hlaw).maximum i ω =
      ENNReal.ofReal (Real.exp (Z i ω)) := by
  filter_upwards [exponential_law_positive_ae μ (Z i) (hZ i) (hlaw i)] with ω hω
  change (⨆ t : ℝ≥0, ENNReal.ofReal (exponentialSurvival t (Z i ω))) = _
  change 0 < Z i ω at hω
  rw [exponential_extended_maximum,if_pos hω]

theorem survivalModel_cost {V I Ω : Type} [Fintype I] [mΩ : MeasurableSpace Ω]
    (A : V → I → Prop) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sources : V → MeasurableSpace Ω) (hsub : ∀ v, sources v ≤ mΩ)
    (hind : iIndep sources μ) (Z : I → Ω → ℝ) (hZ : ∀ i, Measurable (Z i))
    (hsource : ∀ i, Measurable[studyInformation A sources i] (Z i))
    (hlaw : ∀ i, μ.map (Z i) = expMeasure 1) (a : I → ℝ) :
    (survivalModel A μ sources hsub hind Z hZ hsource hlaw).cost a =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (∑ i, a i*Z i ω)) ∂μ := by
  have h := ae_all_iff.mpr (fun i => survivalModel_maximum A μ sources hsub hind Z hZ hsource hlaw i)
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω
  simp_rw [hω,ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),← Real.exp_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.exp_pos _).le),Real.exp_sum]
  simp only [mul_comm]

end RepeatedEvidenceProbability
