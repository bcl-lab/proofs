import ExponentialSurvival
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

/-- Information available from the sources declared for a study. Independent
sigma-algebras represent primitive sources without restricting their value types. -/
def studyInformation {V I Ω : Type} (A : V → I → Prop)
    (sources : V → MeasurableSpace Ω) (i : I) : MeasurableSpace Ω :=
  ⨆ v, ⨆ (_ : A v i), sources v

/-- A complete admissible system. Maxima use extended nonnegative reals, so
unbounded paths are not silently assigned the default real supremum zero.
Initial value one is required almost surely, the usual probability convention. -/
structure MonitoringModel {V I : Type} (A : V → I → Prop) where
  Ω : Type
  [ambient : MeasurableSpace Ω]
  μ : Measure Ω
  [probability : IsProbabilityMeasure μ]
  sources : V → MeasurableSpace Ω
  sources_le : ∀ v, sources v ≤ ambient
  independent : iIndep sources μ
  filtration : I → Filtration ℝ≥0 ambient
  process : I → ℝ≥0 → Ω → ℝ
  valid : ∀ i, Supermartingale (process i) (filtration i) μ
  nonnegative : ∀ i t ω, 0 ≤ process i t ω
  initial : ∀ i, ∀ᵐ ω ∂μ, process i 0 ω = 1
  right_continuous : ∀ i ω t,
    ContinuousWithinAt (fun s => process i s ω) (Ici t) t
  source_measurable : ∀ i t,
    @Measurable Ω ℝ (studyInformation A sources i) _ (process i t)
  maximum_measurable : ∀ i,
    @Measurable Ω ℝ≥0∞ ambient _ (fun ω => ⨆ t, ENNReal.ofReal (process i t ω))

attribute [instance] MonitoringModel.ambient MonitoringModel.probability

noncomputable def MonitoringModel.maximum {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) (ω : model.Ω) : ℝ≥0∞ :=
  ⨆ t, ENNReal.ofReal (model.process i t ω)

noncomputable def MonitoringModel.cost {V I : Type} [Fintype I] {A : V → I → Prop}
    (model : MonitoringModel A) (a : I → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∏ i, model.maximum i ω ^ a i ∂model.μ

/-- The universal cost ranges over all admissible ambient probability spaces,
independent source information, filtrations and complete evidence paths. -/
noncomputable def universalCost {V I : Type} [Fintype I]
    (A : V → I → Prop) (a : I → ℝ) : ℝ≥0∞ :=
  ⨆ model : MonitoringModel A, model.cost a

theorem model_cost_le_universal {V I : Type} [Fintype I] {A : V → I → Prop}
    (model : MonitoringModel A) (a : I → ℝ) : model.cost a ≤ universalCost A a :=
  le_iSup (fun model : MonitoringModel A => model.cost a) model

theorem universalCost_le_iff {V I : Type} [Fintype I] (A : V → I → Prop)
    (a : I → ℝ) (C : ℝ≥0∞) :
    universalCost A a ≤ C ↔ ∀ model : MonitoringModel A, model.cost a ≤ C :=
  iSup_le_iff

/-- All sources but one may be deterministic. The remaining source can have
any probability law, and the resulting family is still mutually independent. -/
theorem independent_single_source {V Ω : Type} [DecidableEq V] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (v : V) :
    iIndep (fun w : V => if w = v then ‹MeasurableSpace Ω› else ⊥) μ := by
  rw [iIndep_iff]
  intro S f hf
  by_cases he : ∃ w ∈ S, f w = ∅
  · obtain ⟨w,hw,he⟩ := he
    have hi : (⋂ i ∈ S, f i) = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro x hx
      have := mem_iInter.mp (mem_iInter.mp hx w) hw
      simpa [he] using this
    rw [hi,measure_empty]
    symm
    exact Finset.prod_eq_zero hw (by simp [he])
  · have htriv : ∀ w ∈ S, w ≠ v → f w = univ := by
      intro w hw hne
      have hm := hf w hw
      rw [if_neg hne, MeasurableSpace.measurableSet_bot_iff] at hm
      exact hm.resolve_left (by intro h; exact he ⟨w,hw,h⟩)
    by_cases hv : v ∈ S
    · have hi : (⋂ i ∈ S, f i) = f v := by
        ext x
        simp only [mem_iInter]
        constructor
        · intro h; exact h v hv
        · intro h w hw
          by_cases hwv : w = v
          · simpa [hwv] using h
          · simp [htriv w hw hwv]
      rw [hi]
      symm
      apply Finset.prod_eq_single v
      · intro w hw hne; simp [htriv w hw hne]
      · exact fun h => (h hv).elim
    · have hi : (⋂ i ∈ S, f i) = univ := by
        ext x
        simp only [mem_iInter, mem_univ, iff_true]
        intro w hw
        simp [htriv w hw (by intro h; exact hv (h ▸ hw))]
      rw [hi, measure_univ]
      symm
      apply Finset.prod_eq_one
      intro w hw
      simp [htriv w hw (by intro h; exact hv (h ▸ hw))]

end RepeatedEvidenceProbability
