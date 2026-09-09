import DiscreteVille
import StochasticModel
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RepeatedEvidenceProbability

def sampledFiltration {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (t : ℕ → ℝ≥0) (ht : Monotone t) :
    Filtration ℕ ‹MeasurableSpace Ω› where
  seq n := ℱ (t n)
  mono' := fun _ _ h => ℱ.mono (ht h)
  le' := fun n => ℱ.le (t n)

theorem sampled_supermartingale {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Supermartingale M ℱ μ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) :
    Supermartingale (fun n => M (t n)) (sampledFiltration ℱ t ht) μ :=
  ⟨fun n => hM.adapted (t n), fun i j hij => hM.condExp_ae_le (ht hij),
    fun n => hM.integrable (t n)⟩

/-- Ville's inequality on any finite set of real monitoring times. The finite
set is sorted into a monotone sampling grid before optional stopping is used. -/
theorem ville_finite_times {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Supermartingale M ℱ μ)
    (h0 : ∀ t ω, 0 ≤ M t ω) (hinit : (∫ ω, M 0 ω ∂μ) ≤ 1)
    (u : ℝ) (hu : 0 < u) (S : Finset ℝ≥0) :
    μ {ω | ∃ t ∈ S, u ≤ M t ω} ≤ ENNReal.ofReal (1/u) := by
  classical
  by_cases hs : S.Nonempty
  · have hc : 0 < S.card := Finset.card_pos.mpr hs
    let e := S.orderEmbOfFin rfl
    let t : ℕ → ℝ≥0 := fun n => e ⟨min n (S.card-1),
      lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hc (by decide))⟩
    have ht : Monotone t := by
      intro j k hjk
      apply e.monotone
      exact min_le_min_right _ hjk
    have hti : (∫ ω, M (t 0) ω ∂μ) ≤ 1 := by
      have h := hM.setIntegral_le (show (0:ℝ≥0) ≤ t 0 from zero_le _) MeasurableSet.univ
      simp only [setIntegral_univ] at h
      exact h.trans hinit
    have hbound := ville_finite_horizon μ (sampledFiltration ℱ t ht) (fun n => M (t n))
      (sampled_supermartingale μ ℱ M hM t ht) (fun n => h0 (t n)) hti u hu (S.card-1)
    apply le_trans (measure_mono _) hbound
    intro ω hω
    obtain ⟨s,hsS,hsM⟩ := hω
    have hr : s ∈ range e := by simpa [e,Finset.range_orderEmbOfFin] using hsS
    obtain ⟨j,hj⟩ := hr
    have hjN : j.val ≤ S.card-1 := Nat.le_sub_one_of_lt j.isLt
    refine ⟨j.val,hjN,?_⟩
    simpa [t,min_eq_left hjN,hj] using hsM
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

/-- A strict crossing of a right-continuous path has a rational-time witness. -/
theorem rational_crossing {f : ℝ≥0 → ℝ}
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t) (u : ℝ) :
    (∃ t, u < f t) ↔ ∃ q : ℚ, u < f (Real.toNNReal (q:ℝ)) := by
  constructor
  · rintro ⟨t,ht⟩
    have hn : {s : ℝ≥0 | u < f s} ∈ 𝓝[≥] t :=
      (hf t).eventually (Ioi_mem_nhds ht)
    obtain ⟨s,hs,hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hn
    obtain ⟨q,hqt,hqs⟩ := exists_rat_btwn (show (t:ℝ) < (s:ℝ) from hs)
    have hq0 : 0 ≤ (q:ℝ) := t.coe_nonneg.trans hqt.le
    refine ⟨q,hsub ⟨?_,?_⟩⟩
    · change (t:ℝ) ≤ (Real.toNNReal (q:ℝ):ℝ)
      simpa [Real.coe_toNNReal _ hq0] using hqt.le
    · change (Real.toNNReal (q:ℝ):ℝ) < (s:ℝ)
      simpa [Real.coe_toNNReal _ hq0] using hqs
  · rintro ⟨q,hq⟩
    exact ⟨_,hq⟩

/-- Continuous-time Ville inequality, derived from local supermartingale
validity and path right continuity. No maximal inequality is assumed. -/
theorem ville_continuous_crossing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (M : ℝ≥0 → Ω → ℝ) (hM : Supermartingale M ℱ μ)
    (h0 : ∀ t ω, 0 ≤ M t ω) (hinit : (∫ ω, M 0 ω ∂μ) ≤ 1)
    (hright : ∀ ω t, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (u : ℝ) (hu : 0 < u) :
    μ {ω | ∃ t, u < M t ω} ≤ ENNReal.ofReal (1/u) := by
  classical
  let B : Finset ℚ → Set Ω := fun S => {ω | ∃ q ∈ S, u < M (Real.toNNReal (q:ℝ)) ω}
  have he : {ω | ∃ t, u < M t ω} = ⋃ S : Finset ℚ, B S := by
    ext ω
    rw [mem_setOf_eq,rational_crossing (hright ω) u]
    simp only [mem_iUnion,B,mem_setOf_eq]
    constructor
    · rintro ⟨q,hq⟩; exact ⟨{q},q,Finset.mem_singleton_self q,hq⟩
    · rintro ⟨S,q,_,hq⟩; exact ⟨q,hq⟩
  have hB : Monotone B := by
    intro S T hST ω
    rintro ⟨q,hq,hqM⟩
    exact ⟨q,hST hq,hqM⟩
  rw [he,hB.directed_le.measure_iUnion]
  apply iSup_le
  intro S
  apply le_trans (measure_mono _) (ville_finite_times μ ℱ M hM h0 hinit u hu
    (S.image fun q : ℚ => Real.toNNReal (q:ℝ)))
  intro ω hω
  obtain ⟨q,hq,hqM⟩ := hω
  exact ⟨_,Finset.mem_image.mpr ⟨q,hq,rfl⟩,hqM.le⟩

theorem MonitoringModel.ville_tail {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) (u : ℝ) (hu : 0 < u) :
    model.μ {ω | ENNReal.ofReal u < model.maximum i ω} ≤ ENNReal.ofReal (1/u) := by
  have he : {ω | ENNReal.ofReal u < model.maximum i ω} =
      {ω | ∃ t, u < model.process i t ω} := by
    ext ω
    simp only [mem_setOf_eq,MonitoringModel.maximum,lt_iSup_iff,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le]
  rw [he]
  apply ville_continuous_crossing model.μ (model.filtration i) (model.process i)
    (model.valid i) (model.nonnegative i) _ (model.right_continuous i) u hu
  calc
    (∫ ω, model.process i 0 ω ∂model.μ) = ∫ _ : model.Ω, (1:ℝ) ∂model.μ :=
      integral_congr_ae (model.initial i)
    _ ≤ 1 := by simp

/-- A path may be unbounded on a null set; the extended maximum is finite
almost surely, as a consequence of Ville's inequality. -/
theorem MonitoringModel.maximum_finite_ae {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) : ∀ᵐ ω ∂model.μ, model.maximum i ω ≠ ∞ := by
  have hz : model.μ {ω | model.maximum i ω = ∞} = 0 := by
    apply le_antisymm _ (zero_le _)
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : 0 < (ε:ℝ) := by exact_mod_cast hε
    have htail := model.ville_tail i (1/(ε:ℝ)) (one_div_pos.mpr hεr)
    have hsub : {ω | model.maximum i ω = ∞} ⊆
        {ω | ENNReal.ofReal (1/(ε:ℝ)) < model.maximum i ω} := by
      intro ω hω
      change model.maximum i ω = ∞ at hω
      simp [hω]
    have h := (measure_mono hsub).trans htail
    simpa using h
  apply ae_iff.mpr
  simpa using hz

/-- Sharp power-moment calibration for the actual continuous running maximum
of every admissible local process. No tail or moment premise remains. -/
theorem MonitoringModel.maximum_power_moment {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫⁻ ω, model.maximum i ω ^ p ∂model.μ) ≤ ENNReal.ofReal (1/(1-p)) := by
  have hreal := ville_tail_power_moment model.μ (fun ω => (model.maximum i ω).toReal)
    (model.maximum_measurable i).ennreal_toReal.aemeasurable
    (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    (fun u hu => ?_) p hp hp1
  · convert hreal using 1
    apply lintegral_congr_ae
    filter_upwards [model.maximum_finite_ae i] with ω hω
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le, ENNReal.ofReal_toReal hω]
  · apply le_trans (measure_mono_ae _) (model.ville_tail i u (zero_lt_one.trans_le hu))
    filter_upwards [model.maximum_finite_ae i] with ω hω
    exact (ENNReal.ofReal_lt_iff_lt_toReal (zero_le_one.trans hu) hω).mpr

theorem right_continuous_maximum_eq_rational {f : ℝ≥0 → ℝ}
    (hf : ∀ t, ContinuousWithinAt f (Ici t) t) :
    (⨆ t, ENNReal.ofReal (f t)) = ⨆ q : ℚ, ENNReal.ofReal (f (Real.toNNReal (q:ℝ))) := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hr' : ENNReal.ofReal (r:ℝ) < ⨆ t, ENNReal.ofReal (f t) := by simpa using hr
    obtain ⟨t,ht⟩ := lt_iSup_iff.mp hr'
    obtain ⟨q,hq⟩ := (rational_crossing hf (r:ℝ)).1
      ⟨t,(ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.coe_nonneg).1 ht⟩
    have hq' := ENNReal.ofReal_le_ofReal hq.le
    exact le_iSup_of_le q (by simpa using hq')
  · exact iSup_le fun q => le_iSup (fun t => ENNReal.ofReal (f t)) _

/-- The running maximum retains source compatibility. This is derived from
path measurability and right continuity, not inserted as a model assumption. -/
theorem MonitoringModel.maximum_source_measurable {V I : Type} {A : V → I → Prop}
    (model : MonitoringModel A) (i : I) :
    @Measurable model.Ω ℝ≥0∞ (studyInformation A model.sources i) _ (model.maximum i) := by
  have he : model.maximum i = fun ω =>
      ⨆ q : ℚ, ENNReal.ofReal (model.process i (Real.toNNReal (q:ℝ)) ω) := by
    funext ω
    exact right_continuous_maximum_eq_rational (model.right_continuous i ω)
  rw [he]
  exact Measurable.iSup fun q => (model.source_measurable i _).ennreal_ofReal

end RepeatedEvidenceProbability
