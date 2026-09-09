import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.FactorsThrough

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

/-- Holder with unused exponent mass assigned to the constant one. -/
theorem holder_subprobability_weights {Ω I : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset I)
    (f : I → Ω → ℝ≥0∞) (p : I → ℝ)
    (hf : ∀ i ∈ s, Measurable (f i)) (hp : ∀ i ∈ s, 0 ≤ p i)
    (hs : ∑ i ∈ s, p i ≤ 1) :
    (∫⁻ x, ∏ i ∈ s, f i x ^ p i ∂μ) ≤
      ∏ i ∈ s, (∫⁻ x, f i x ∂μ) ^ p i := by
  have h := ENNReal.lintegral_mul_prod_norm_pow_le (μ := μ) s
    (g := fun _ => 1) aemeasurable_const (fun i hi => (hf i hi).aemeasurable)
    (1 - ∑ i ∈ s, p i) (p := p) (sub_add_cancel _ _)
    (sub_nonneg.mpr hs) hp
  simpa using h

/-- Functions independent of the integrated variable can be factored out;
only the remaining functions consume Holder exponent mass. -/
theorem holder_with_constant_complement {Ω I : Type} [MeasurableSpace Ω]
    [Fintype I] (μ : Measure Ω) [IsProbabilityMeasure μ] (s : Finset I)
    (f : I → Ω → ℝ≥0∞) (p : I → ℝ) (x₀ : Ω)
    (hf : ∀ i, Measurable (f i)) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i ∈ s, p i ≤ 1)
    (hc : ∀ i ∉ s, ∀ x, f i x = f i x₀) :
    (∫⁻ x, ∏ i, f i x ^ p i ∂μ) ≤
      ∏ i, (∫⁻ x, f i x ∂μ) ^ p i := by
  classical
  have hprod (x : Ω) : (∏ i, f i x ^ p i) =
      (∏ i ∈ s, f i x ^ p i) * ∏ i ∈ sᶜ, f i x₀ ^ p i := by
    rw [← Finset.prod_mul_prod_compl s]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [hc i (Finset.mem_compl.mp hi)]
  have hint (i : I) (hi : i ∈ sᶜ) : (∫⁻ x, f i x ∂μ) = f i x₀ := by
    simp_rw [hc i (Finset.mem_compl.mp hi)]
    simp
  simp_rw [hprod]
  rw [lintegral_mul_const _ (s.measurable_prod (fun i _ => (hf i).pow_const _))]
  calc
    _ ≤ (∏ i ∈ s, (∫⁻ x, f i x ∂μ) ^ p i) * ∏ i ∈ sᶜ, f i x₀ ^ p i :=
      mul_le_mul_right' (holder_subprobability_weights μ s f p
        (fun i _ => hf i) (fun i _ => hp i) hs) _
    _ = ∏ i, (∫⁻ x, f i x ∂μ) ^ p i := by
      rw [← Finset.prod_mul_prod_compl s]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      rw [hint i hi]

/-- Tonelli after splitting the first coordinate of a finite product. -/
theorem lintegral_pi_fin_succ {n : ℕ} {X : Fin (n+1) → Type}
    [∀ v, MeasurableSpace (X v)] (μ : ∀ v, Measure (X v))
    [∀ v, IsProbabilityMeasure (μ v)]
    (f : (∀ v, X v) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂Measure.pi μ) =
      ∫⁻ y, ∫⁻ x, f (Fin.cons x y) ∂μ 0 ∂Measure.pi (fun v => μ v.succ) := by
  have h := ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp hf
  simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero] at h
  rw [lintegral_prod_symm] at h
  · simpa using h.symm
  · simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero] using
      (hf.comp (MeasurableEquiv.piFinSuccAbove X 0).symm.measurable).aemeasurable

/-- Finner's inequality for arbitrary measurable functions of finitely many
independent coordinates. Incidence is enforced by the actual dependence of
each function, and the inequality itself is proved by coordinate induction. -/
theorem finner_product_fin {I : Type} [Fintype I] (n : ℕ)
    {X : Fin n → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, Nonempty (X v)] (μ : ∀ v, Measure (X v))
    [∀ v, IsProbabilityMeasure (μ v)]
    (A : Fin n → I → Prop) [DecidableRel A]
    (f : I → (∀ v, X v) → ℝ≥0∞) (p : I → ℝ)
    (hf : ∀ i, Measurable (f i)) (hp : ∀ i, 0 ≤ p i)
    (hload : ∀ v, (∑ i, if A v i then p i else 0) ≤ 1)
    (hdep : ∀ i x y, (∀ v, A v i → x v = y v) → f i x = f i y) :
    (∫⁻ x, ∏ i, f i x ^ p i ∂Measure.pi μ) ≤
      ∏ i, (∫⁻ x, f i x ∂Measure.pi μ) ^ p i := by
  classical
  induction n with
  | zero =>
    let z : ∀ v, X v := fun v => Fin.elim0 v
    have hc : ∀ i x, f i x = f i z := by
      intro i x
      apply hdep
      intro v
      exact Fin.elim0 v
    simp_rw [hc]
    simp
  | succ n ih =>
    have hm : Measurable (fun z : X 0 × (∀ v : Fin n, X v.succ) =>
        Fin.cons z.1 z.2) := by
      apply measurable_pi_iff.mpr
      intro v
      refine Fin.cases ?_ ?_ v
      · exact measurable_fst
      · intro j
        exact (measurable_pi_apply j).comp measurable_snd
    let g (i : I) (y : ∀ v : Fin n, X v.succ) : ℝ≥0∞ :=
      ∫⁻ x, f i (Fin.cons x y) ∂μ 0
    have hg : ∀ i, Measurable (g i) := fun i =>
      ((hf i).comp hm).lintegral_prod_left'
    have hdg : ∀ i y z, (∀ v : Fin n, A v.succ i → y v = z v) →
        g i y = g i z := by
      intro i y z hyz
      apply lintegral_congr
      intro x
      apply hdep
      intro v
      refine Fin.cases ?_ ?_ v
      · intro _; rfl
      · intro j hj
        exact hyz j hj
    have hstep (y : ∀ v : Fin n, X v.succ) :
        (∫⁻ x, ∏ i, f i (Fin.cons x y) ^ p i ∂μ 0) ≤ ∏ i, g i y ^ p i := by
      apply holder_with_constant_complement (μ 0)
        (Finset.univ.filter (fun i => A 0 i))
        (fun i x => f i (Fin.cons x y)) p (Classical.arbitrary (X 0))
      · intro i
        exact (hf i).comp (hm.comp (measurable_id.prodMk measurable_const))
      · exact hp
      · simpa only [Finset.sum_filter] using hload 0
      · intro i hi x
        have hi : ¬ A 0 i := by simpa using hi
        apply hdep
        intro v
        refine Fin.cases ?_ ?_ v
        · intro h; exact (hi h).elim
        · intro j _; rfl
    rw [lintegral_pi_fin_succ μ _
      (Finset.univ.measurable_prod (fun i _ => (hf i).pow_const _))]
    calc
      _ ≤ ∫⁻ y, ∏ i, g i y ^ p i ∂Measure.pi (fun v => μ v.succ) :=
        lintegral_mono hstep
      _ ≤ ∏ i, (∫⁻ y, g i y ∂Measure.pi (fun v => μ v.succ)) ^ p i :=
        ih (fun v => μ v.succ) (fun v i => A v.succ i) g hg
          (fun v => hload v.succ) hdg
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        rw [lintegral_pi_fin_succ μ (f i) (hf i)]

/-- The coordinate induction is independent of the naming of the source set. -/
theorem finner_product {V I : Type} [Fintype V] [Fintype I]
    {X : V → Type} [∀ v, MeasurableSpace (X v)] [∀ v, Nonempty (X v)]
    (μ : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (μ v)]
    (A : V → I → Prop) [DecidableRel A]
    (f : I → (∀ v, X v) → ℝ≥0∞) (p : I → ℝ)
    (hf : ∀ i, Measurable (f i)) (hp : ∀ i, 0 ≤ p i)
    (hload : ∀ v, (∑ i, if A v i then p i else 0) ≤ 1)
    (hdep : ∀ i x y, (∀ v, A v i → x v = y v) → f i x = f i y) :
    (∫⁻ x, ∏ i, f i x ^ p i ∂Measure.pi μ) ≤
      ∏ i, (∫⁻ x, f i x ∂Measure.pi μ) ^ p i := by
  let e := (Fintype.equivFin V).symm
  let E := MeasurableEquiv.piCongrLeft X e
  have hE := measurePreserving_piCongrLeft μ e
  have h := finner_product_fin (Fintype.card V) (fun v => μ (e v))
    (fun v i => A (e v) i) (fun i x => f i (E x)) p
    (fun i => (hf i).comp E.measurable) hp (fun v => hload (e v)) ?_
  · calc
      _ = ∫⁻ x, ∏ i, f i (E x) ^ p i ∂Measure.pi (fun v => μ (e v)) :=
        (hE.lintegral_comp
          (Finset.univ.measurable_prod (fun i _ => (hf i).pow_const _))).symm
      _ ≤ ∏ i, (∫⁻ x, f i (E x) ∂Measure.pi (fun v => μ (e v))) ^ p i := h
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        rw [hE.lintegral_comp (hf i)]
  · intro i x y hxy
    apply hdep
    intro v hv
    obtain ⟨w,rfl⟩ := e.surjective v
    simpa only [E,MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply] using hxy w hv

end RepeatedEvidenceProbability
