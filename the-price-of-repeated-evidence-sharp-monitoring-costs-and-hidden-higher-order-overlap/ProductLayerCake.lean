import QuantileCore
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory Set
open scoped ENNReal

namespace RepeatedEvidenceProbability

noncomputable def positiveRay : Measure ℝ := volume.restrict (Ioi (0:ℝ))

instance positiveRay_sFinite : SFinite positiveRay := inferInstanceAs (SFinite (volume.restrict _))

theorem threshold_integral (x : ℝ) :
    (∫⁻ s, if s < x then (1:ℝ≥0∞) else 0 ∂positiveRay) = ENNReal.ofReal x := by
  change (∫⁻ s, (Iio x).indicator (fun _ => (1:ℝ≥0∞)) s ∂positiveRay) = _
  rw [lintegral_indicator_const measurableSet_Iio,one_mul,positiveRay,
    Measure.restrict_apply measurableSet_Iio,Iio_inter_Ioi,Real.volume_Ioo,sub_zero]

/-- Double layer-cake identity, allowing infinite expectations. -/
theorem product_layercake {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (g x) ∂μ) =
      ∫⁻ s, ∫⁻ t, μ {x | s < f x ∧ t < g x} ∂positiveRay ∂positiveRay := by
  classical
  have hth (x : ℝ) : Measurable (fun s : ℝ => if s < x then (1:ℝ≥0∞) else 0) :=
    measurable_const.ite measurableSet_Iio measurable_const
  have hfirst : Measurable (fun p : Ω × ℝ =>
      (if p.2 < f p.1 then (1:ℝ≥0∞) else 0) * ENNReal.ofReal (g p.1)) :=
    (measurable_const.ite (measurableSet_lt measurable_snd (hf.comp measurable_fst))
      measurable_const).mul (hg.comp measurable_fst).ennreal_ofReal
  calc
    _ = ∫⁻ x, ∫⁻ s, (if s < f x then (1:ℝ≥0∞) else 0) *
        ENNReal.ofReal (g x) ∂positiveRay ∂μ := by
      apply lintegral_congr
      intro x
      rw [lintegral_mul_const _ (hth _),threshold_integral]
    _ = ∫⁻ s, ∫⁻ x, (if s < f x then (1:ℝ≥0∞) else 0) *
        ENNReal.ofReal (g x) ∂μ ∂positiveRay :=
      lintegral_lintegral_swap hfirst.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro s
      have hsecond : Measurable (fun p : Ω × ℝ =>
          (if s < f p.1 then (1:ℝ≥0∞) else 0) *
            (if p.2 < g p.1 then (1:ℝ≥0∞) else 0)) :=
        (measurable_const.ite (measurableSet_lt measurable_const (hf.comp measurable_fst))
          measurable_const).mul
          (measurable_const.ite (measurableSet_lt measurable_snd (hg.comp measurable_fst))
            measurable_const)
      calc
        _ = ∫⁻ x, ∫⁻ t, (if s < f x then (1:ℝ≥0∞) else 0) *
            (if t < g x then (1:ℝ≥0∞) else 0) ∂positiveRay ∂μ := by
          apply lintegral_congr
          intro x
          rw [lintegral_const_mul _ (hth _),threshold_integral]
        _ = ∫⁻ t, ∫⁻ x, (if s < f x then (1:ℝ≥0∞) else 0) *
            (if t < g x then (1:ℝ≥0∞) else 0) ∂μ ∂positiveRay :=
          lintegral_lintegral_swap hsecond.aemeasurable
        _ = _ := by
          apply lintegral_congr
          intro t
          have he : (fun x => (if s < f x then (1:ℝ≥0∞) else 0) *
              (if t < g x then (1:ℝ≥0∞) else 0)) =
              {x | s < f x ∧ t < g x}.indicator (fun _ => (1:ℝ≥0∞)) := by
            funext x
            simp only [indicator_apply,mem_setOf_eq]
            split_ifs <;> simp_all
          rw [he]
          have hm : MeasurableSet {x | s < f x ∧ t < g x} :=
            (measurableSet_lt measurable_const hf).inter
              (measurableSet_lt measurable_const hg)
          exact lintegral_indicator_one hm

end RepeatedEvidenceProbability
