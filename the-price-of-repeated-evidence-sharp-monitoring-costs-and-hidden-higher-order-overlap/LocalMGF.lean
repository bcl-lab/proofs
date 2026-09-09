import Mathlib.Probability.Moments.ComplexMGF

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RepeatedEvidenceProbability

/-- Equality of moment generating functions on a neighborhood of zero
determines the law. Local exponential integrability is explicit. -/
theorem law_eq_of_mgf_near_zero {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (ε : ℝ) (hε : 0 < ε)
    (hiX : ∀ t ∈ Ioo (-ε) ε, Integrable (fun ω => Real.exp (t*X ω)) μ)
    (hiY : ∀ t ∈ Ioo (-ε) ε, Integrable (fun ω => Real.exp (t*Y ω)) ν)
    (heq : ∀ t ∈ Ioo (-ε) ε, mgf X μ t = mgf Y ν t) :
    μ.map X = ν.map Y := by
  let S : Set ℂ := {z | z.re ∈ Ioo (-ε) ε}
  have hIX : Ioo (-ε) ε ⊆ interior (integrableExpSet X μ) :=
    isOpen_Ioo.subset_interior_iff.mpr hiX
  have hIY : Ioo (-ε) ε ⊆ interior (integrableExpSet Y ν) :=
    isOpen_Ioo.subset_interior_iff.mpr hiY
  have hAX : AnalyticOnNhd ℂ (complexMGF X μ) S := fun z hz => analyticAt_complexMGF (hIX hz)
  have hAY : AnalyticOnNhd ℂ (complexMGF Y ν) S := fun z hz => analyticAt_complexMGF (hIY hz)
  have hS : IsPreconnected S := ((convex_Ioo (-ε) ε).linear_preimage Complex.reLm).isPreconnected
  have hzero : (0:ℂ) ∈ S := by
    change -ε < (0:ℂ).re ∧ (0:ℂ).re < ε
    simpa using And.intro (neg_neg_iff_pos.mpr hε) hε
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] 0, complexMGF X μ z = complexMGF Y ν z := by
    have hre : ∀ᶠ t : ℝ in 𝓝[≠] 0, complexMGF X μ t = complexMGF Y ν t := by
      have hn : Ioo (-ε) ε ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by linarith) hε
      filter_upwards [mem_nhdsWithin_of_mem_nhds hn] with t ht
      rw [complexMGF_ofReal,complexMGF_ofReal,heq t ht]
    have hre' := hre.frequently
    rw [frequently_iff_seq_forall] at hre' ⊢
    obtain ⟨xs,ht,he⟩ := hre'
    refine ⟨fun n => (xs n:ℂ),?_,fun n => he n⟩
    rw [tendsto_nhdsWithin_iff] at ht ⊢
    constructor
    · simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp ht.1
    · simpa using ht.2
  have hall : EqOn (complexMGF X μ) (complexMGF Y ν) S :=
    hAX.eqOn_of_preconnected_of_frequently_eq hAY hS hzero hfreq
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I hX.aemeasurable,← complexMGF_mul_I hY.aemeasurable]
  apply hall
  simpa [S] using And.intro (neg_neg_iff_pos.mpr hε) hε

end RepeatedEvidenceProbability
