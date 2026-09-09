import Mathlib.Probability.Martingale.Basic

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RepeatedEvidenceProbability

variable {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]

/-- Events may reveal everything outside the surviving set, but cannot distinguish
between two outcomes that are both still alive. -/
def survivalSpace (A : Set Ω) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet s ∧ ∀ x ∈ A, ∀ y ∈ A, (x ∈ s ↔ y ∈ s)
  measurableSet_empty := ⟨MeasurableSet.empty, by simp⟩
  measurableSet_compl := by
    intro s hs
    exact ⟨hs.1.compl, fun x hx y hy => not_congr (hs.2 x hx y hy)⟩
  measurableSet_iUnion := by
    intro f hf
    refine ⟨MeasurableSet.iUnion (fun i => (hf i).1), ?_⟩
    intro x hx y hy
    simp only [mem_iUnion]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i, ((hf i).2 x hx y hy).1 hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨i, ((hf i).2 x hx y hy).2 hi⟩

/-- An antitone family of surviving events gives an increasing filtration. -/
def survivalFiltration (A : ι → Set Ω) (hA : Antitone A) : Filtration ι ‹MeasurableSpace Ω› where
  seq t := survivalSpace (A t)
  mono' := by
    intro s t hst E hE
    exact ⟨hE.1, fun x hx y hy => hE.2 x (hA hst hx) y (hA hst hy)⟩
  le' := fun _ _ hE => hE.1

/-- A survival indicator divided by its unconditional survival probability. -/
noncomputable def survivalProcess (μ : Measure Ω) (A : ι → Set Ω) (t : ι) : Ω → ℝ :=
  (A t).indicator (fun _ => (μ.real (A t))⁻¹)

lemma alive_measurable (A : Set Ω) (hA : MeasurableSet A) : MeasurableSet[survivalSpace A] A :=
  ⟨hA, fun _ hx _ hy => iff_of_true hx hy⟩

lemma survival_adapted (μ : Measure Ω) (A : ι → Set Ω) (hA : Antitone A)
    (hm : ∀ t, MeasurableSet (A t)) :
    Adapted (survivalFiltration A hA) (survivalProcess μ A) := by
  intro t
  exact stronglyMeasurable_const.indicator (alive_measurable (A t) (hm t))

lemma survival_integrable (μ : Measure Ω) [IsFiniteMeasure μ] (A : ι → Set Ω)
    (hm : ∀ t, MeasurableSet (A t)) (t : ι) : Integrable (survivalProcess μ A t) μ :=
  (integrable_const _).indicator (hm t)

lemma survival_setIntegral (μ : Measure Ω) [IsFiniteMeasure μ] (A : ι → Set Ω)
    (hm : ∀ t, MeasurableSet (A t)) (t : ι) (E : Set Ω) :
    ∫ ω in E, survivalProcess μ A t ω ∂μ = μ.real (E ∩ A t) * (μ.real (A t))⁻¹ := by
  rw [survivalProcess, setIntegral_indicator (hm t), setIntegral_const, smul_eq_mul]

/-- Integral preservation on every event known at the earlier time. No
conditional-expectation or martingale property is assumed. -/
lemma survival_setIntegral_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ι → Set Ω) (hA : Antitone A) (hm : ∀ t, MeasurableSet (A t))
    (hp : ∀ t, μ.real (A t) ≠ 0) {s t : ι} (hst : s ≤ t)
    (E : Set Ω) (hE : MeasurableSet[survivalFiltration A hA s] E) :
    ∫ ω in E, survivalProcess μ A s ω ∂μ = ∫ ω in E, survivalProcess μ A t ω ∂μ := by
  rw [survival_setIntegral μ A hm s E, survival_setIntegral μ A hm t E]
  by_cases he : ∃ x ∈ A s, x ∈ E
  · obtain ⟨x,hx,hxE⟩ := he
    have has : A s ⊆ E := fun y hy => (hE.2 x hx y hy).1 hxE
    have hat : A t ⊆ E := (hA hst).trans has
    rw [inter_eq_right.mpr has, inter_eq_right.mpr hat,
      mul_inv_cancel₀ (hp s), mul_inv_cancel₀ (hp t)]
  · have hsE : E ∩ A s = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro x hx
      exact he ⟨x,hx.2,hx.1⟩
    have htE : E ∩ A t = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro x hx
      exact he ⟨x,hA hst hx.2,hx.1⟩
    simp [hsE,htE]

/-- The complete martingale property for normalized survival indicators on any
finite measure space and any preordered time set with nonzero survival mass. -/
theorem survival_martingale (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ι → Set Ω) (hA : Antitone A) (hm : ∀ t, MeasurableSet (A t))
    (hp : ∀ t, μ.real (A t) ≠ 0) :
    Martingale (survivalProcess μ A) (survivalFiltration A hA) μ := by
  refine ⟨survival_adapted μ A hA hm, ?_⟩
  intro s t hst
  apply Filter.EventuallyEq.symm
  exact ae_eq_condExp_of_forall_setIntegral_eq (survivalFiltration A hA |>.le s)
    (survival_integrable μ A hm t)
    (fun E _ _ => (survival_integrable μ A hm s).integrableOn)
    (fun E hE _ => survival_setIntegral_eq μ A hA hm hp hst E hE)
    ((survival_adapted μ A hA hm s).aestronglyMeasurable)

theorem survival_nonnegative (μ : Measure Ω) (A : ι → Set Ω) (t : ι) (ω : Ω) :
    0 ≤ survivalProcess μ A t ω := by
  exact indicator_nonneg (fun _ _ => inv_nonneg.mpr ENNReal.toReal_nonneg) ω

theorem survival_mean_one (μ : Measure Ω) [IsFiniteMeasure μ] (A : ι → Set Ω)
    (hm : ∀ t, MeasurableSet (A t)) (hp : ∀ t, μ.real (A t) ≠ 0) (t : ι) :
    ∫ ω, survivalProcess μ A t ω ∂μ = 1 := by
  rw [survivalProcess, integral_indicator_const _ (hm t), smul_eq_mul, mul_inv_cancel₀ (hp t)]

end RepeatedEvidenceProbability
