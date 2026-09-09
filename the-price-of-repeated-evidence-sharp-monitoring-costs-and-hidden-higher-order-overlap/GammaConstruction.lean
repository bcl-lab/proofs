import GammaSums
import IndependentCoordinates
import UniversalDivergence
import ContinuousVille
import Mathlib.Probability.Integration

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace RepeatedEvidenceProbability

/-- The survival construction can be used on any ambient space once the
survival time's exponential law has been proved. -/
theorem exponential_law_survival_martingale {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (hlaw : μ.map Z = expMeasure 1) :
    Martingale (fun t ω => exponentialSurvival t (Z ω))
      (survivalFiltration (fun t : ℝ≥0 => {ω | (t:ℝ) < Z ω})
        (fun s t h ω hω => lt_of_le_of_lt (show (s:ℝ) ≤ (t:ℝ) from h) hω)) μ := by
  have hmass (t : ℝ≥0) : μ.real {ω | (t:ℝ) < Z ω} = Real.exp (-(t:ℝ)) := by
    rw [← exponential_survival_mass t,← hlaw]
    simp only [measureReal_def,Measure.map_apply hZ measurableSet_Ioi]
    rfl
  have he : (fun t ω => exponentialSurvival t (Z ω)) =
      survivalProcess μ (fun t : ℝ≥0 => {ω | (t:ℝ) < Z ω}) := by
    funext t ω
    simp [exponentialSurvival,survivalProcess,hmass,Real.exp_neg,indicator_apply]
  rw [he]
  exact survival_martingale _ _ _ (fun t => measurableSet_lt measurable_const hZ)
    (fun t => by rw [hmass]; exact (Real.exp_pos _).ne')

theorem exponential_law_positive_ae {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ) (hZ : Measurable Z) (hlaw : μ.map Z = expMeasure 1) :
    ∀ᵐ ω ∂μ, 0 < Z ω := by
  have h := exponential_positive_ae
  rw [← hlaw] at h
  exact (ae_map_iff hZ.aemeasurable (measurableSet_Ioi)).1 h

noncomputable def gammaProduct {V : Type} [Fintype V] (q : V → ℝ) : Measure (V → ℝ) :=
  Measure.pi (fun v => gammaShapeMeasure (q v))

instance gammaProduct_probability {V : Type} [Fintype V] (q : V → ℝ)
    [∀ v, IsProbabilityMeasure (gammaShapeMeasure (q v))] :
    IsProbabilityMeasure (gammaProduct q) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun v => gammaShapeMeasure (q v))))

noncomputable def gammaStudySum {V I : Type} [Fintype V]
    (A : V → I → Prop) [DecidableRel A] (i : I) (ω : V → ℝ) : ℝ :=
  ∑ v, if A v i then ω v else 0

theorem gammaStudySum_measurable {V I : Type} [Fintype V]
    (A : V → I → Prop) [DecidableRel A] (i : I) : Measurable (gammaStudySum A i) := by
  apply Finset.univ.measurable_sum
  intro v _
  split_ifs
  · exact measurable_pi_apply v
  · exact measurable_const

theorem gammaStudySum_law {V I : Type} [Fintype V]
    (A : V → I → Prop) [DecidableRel A] (q : V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (hbalance : ∀ i, (∑ v, if A v i then q v else 0) = 1) (i : I) :
    (gammaProduct q).map (gammaStudySum A i) = expMeasure 1 := by
  letI : ∀ v, IsProbabilityMeasure (gammaShapeMeasure (q v)) := fun v => gammaShape_probability _ (hq v)
  let G (v : V) (ω : V → ℝ) := if A v i then ω v else 0
  have hG : ∀ v, Measurable (G v) := by
    intro v
    dsimp [G]
    split_ifs
    · exact measurable_pi_apply v
    · exact measurable_const
  have hi : iIndepFun G (gammaProduct q) := by
    exact (probability_pi_coordinates_independent (fun v => gammaShapeMeasure (q v))).comp
      (fun v z => if A v i then z else 0) (fun v => by
        dsimp only
        split_ifs
        · exact measurable_id
        · exact measurable_const)
  have h := independent_gamma_sum_law (gammaProduct q) G (fun v => if A v i then q v else 0)
    (fun v => by dsimp only; split_ifs; exact hq v; rfl) hG hi ?_
  · rw [hbalance] at h
    simpa [gammaStudySum,G,gammaShapeMeasure,expMeasure] using h
  · intro v
    by_cases hv : A v i
    · simpa [G,hv,gammaProduct] using probability_pi_coordinate_law
        (fun v => gammaShapeMeasure (q v)) v
    · simp [G,hv,gammaShapeMeasure]

def coordinateInformation {V : Type} (v : V) : MeasurableSpace (V → ℝ) :=
  (inferInstance : MeasurableSpace ℝ).comap (fun ω => ω v)

theorem gammaStudySum_source_measurable {V I : Type} [Fintype V]
    (A : V → I → Prop) [DecidableRel A] (i : I) :
    Measurable[studyInformation A coordinateInformation i] (gammaStudySum A i) := by
  apply Finset.univ.measurable_sum
  intro v _
  split_ifs with hv
  · rw [measurable_iff_comap_le]
    exact le_iSup_of_le v (le_iSup_of_le hv le_rfl)
  · exact measurable_const

/-- An explicit admissible model from any gamma balancing certificate. -/
noncomputable def balancedGammaModel {V I : Type} [Fintype V]
    (A : V → I → Prop) [DecidableRel A] (q : V → ℝ) (hq : ∀ v, 0 ≤ q v)
    (hbalance : ∀ i, (∑ v, if A v i then q v else 0) = 1) : MonitoringModel A := by
  letI : ∀ v, IsProbabilityMeasure (gammaShapeMeasure (q v)) := fun v => gammaShape_probability _ (hq v)
  exact {
    Ω := V → ℝ
    μ := gammaProduct q
    sources := coordinateInformation
    sources_le := fun v => le_iSup (fun w => coordinateInformation w) v
    independent := by
      have h := probability_pi_coordinates_independent (fun v => gammaShapeMeasure (q v))
      exact (iIndepFun_iff_iIndep _ _ _).1 h
    filtration := fun i => survivalFiltration (fun t : ℝ≥0 => {ω | (t:ℝ) < gammaStudySum A i ω})
      (fun s t h ω hω => lt_of_le_of_lt (show (s:ℝ) ≤ (t:ℝ) from h) hω)
    process := fun i t ω => exponentialSurvival t (gammaStudySum A i ω)
    valid := fun i => (exponential_law_survival_martingale (gammaProduct q) (gammaStudySum A i)
      (gammaStudySum_measurable A i) (gammaStudySum_law A q hq hbalance i)).supermartingale
    nonnegative := fun _ _ _ => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    initial := fun i => (exponential_law_positive_ae (gammaProduct q) (gammaStudySum A i)
      (gammaStudySum_measurable A i) (gammaStudySum_law A q hq hbalance i)).mono
        (fun ω hω => exponential_initial _ hω)
    right_continuous := fun _ ω t => exponential_survival_right_continuous _ t
    source_measurable := fun i _ => (measurable_const.indicator measurableSet_Ioi).comp
      (gammaStudySum_source_measurable A i)
    maximum_measurable := fun i => exponential_extended_maximum_measurable.comp
      (gammaStudySum_measurable A i)
  }

end RepeatedEvidenceProbability
