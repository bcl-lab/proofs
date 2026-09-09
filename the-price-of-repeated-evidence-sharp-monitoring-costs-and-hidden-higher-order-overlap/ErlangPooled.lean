import ErlangCDF
import EqualLeafGamma

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem weightedExponential_cdf_scaling (J : Type) [Fintype J] (c t : ℝ) (hc : 0 < c) :
    cdf (weightedExponentialLaw (fun _ : J => c)) (c*t) =
      cdf (gammaShapeMeasure (Fintype.card J)) t := by
  haveI := gammaShape_probability (Fintype.card J) (Nat.cast_nonneg _)
  rw [cdf_eq_real,cdf_eq_real,measureReal_def,measureReal_def]
  rw [weightedExponentialLaw,Measure.map_apply (weightedSum_measurable _) measurableSet_Iic,
    ← leafSum_gamma_law J,Measure.map_apply (leafSum_measurable J) measurableSet_Iic]
  congr 2
  ext x
  simp only [mem_preimage,mem_Iic,weightedSum_equal_leaves]
  exact mul_le_mul_left hc

theorem pooled_equal_leaf_gamma_integral (J : Type) [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ c : ℝ) (ha₀ : 0 < a₀) (hc : 0 < c) :
    universalCost pooledUses (pooledPowers a₀ (fun _ : J => c)) =
      ∫⁻ t, ENNReal.ofReal (Real.exp (c*t) *
        (1-cdf (gammaShapeMeasure (Fintype.card J)) t)^(-a₀))
        ∂gammaShapeMeasure (Fintype.card J) := by
  haveI := gammaShape_probability (Fintype.card J) (Nat.cast_nonneg _)
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (c*t) *
      (1-cdf (gammaShapeMeasure (Fintype.card J)) t)^(-a₀))) :=
    ((measurable_const.mul measurable_id).exp.mul
      ((measurable_const.sub (monotone_cdf _).measurable).pow_const _)).ennreal_ofReal
  have he := lintegral_map (μ:=exponentialProduct J) hm (leafSum_measurable J)
  rw [leafSum_gamma_law J] at he
  rw [pooled_survival_formula a₀ _ ha₀ (fun _ => hc),he]
  apply lintegral_congr
  intro x
  rw [weightedSum_equal_leaves,weightedExponential_cdf_scaling J c _ hc]

theorem erlang_pooled_integrand (n : ℕ) (a₀ c t : ℝ) (ht : 0 < t) :
    gammaPDF (n+1) 1 t * ENNReal.ofReal (Real.exp (c*t) *
      (1-cdf (gammaMeasure (n+1) 1) t)^(-a₀)) =
      ENNReal.ofReal ((1/(n.factorial:ℝ)) *
        (t^n*Real.exp (-(1-c-a₀)*t)*(erlangPolynomial n t)^(-a₀))) := by
  have hS := erlangPolynomial_pos n t ht.le
  have hD : 0 ≤ erlangDensity n t := by dsimp [erlangDensity]; positivity
  have he : 1-cdf (gammaMeasure (n+1) 1) t = Real.exp (-t)*erlangPolynomial n t := by
    rw [erlang_cdf_formula n t ht.le]
    ring
  rw [gammaPDF,gammaPDF_erlang n t ht.le,← ENNReal.ofReal_mul hD,he,
    Real.mul_rpow (Real.exp_pos _).le hS.le,← Real.exp_mul]
  congr 1
  dsimp [erlangDensity]
  have hx : Real.exp (-t)*Real.exp (c*t)*Real.exp (-t * -a₀) = Real.exp (-(1-c-a₀)*t) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  rw [← hx]
  ring

/-- The additional equal-leaf Erlang quadrature formula in Section 5. -/
theorem pooled_erlang_integral (J : Type) [Fintype J] [DecidableEq J]
    (n : ℕ) (hcard : Fintype.card J = n+1) (a₀ c : ℝ) (ha₀ : 0 < a₀) (hc : 0 < c) :
    universalCost pooledUses (pooledPowers a₀ (fun _ : J => c)) =
      ENNReal.ofReal (1/(n.factorial:ℝ)) * ∫⁻ t in Ioi (0:ℝ),
        ENNReal.ofReal (t^n*Real.exp (-(1-c-a₀)*t)*(erlangPolynomial n t)^(-a₀)) := by
  haveI : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have hk : (Fintype.card J : ℝ) = n+1 := by exact_mod_cast hcard
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hg : gammaShapeMeasure (Fintype.card J) = gammaMeasure (n+1) 1 := by
    rw [hk,gammaShapeMeasure,if_neg hn]
  have hPDF : Measurable (gammaPDF (n+1) 1) := (measurable_gammaPDFReal _ _).ennreal_ofReal
  rw [pooled_equal_leaf_gamma_integral J a₀ c ha₀ hc,hg,gammaMeasure,
    lintegral_withDensity_eq_lintegral_mul volume hPDF]
  · have hφ : Measurable (fun t : ℝ => ENNReal.ofReal
        (t^n*Real.exp (-(1-c-a₀)*t)*(erlangPolynomial n t)^(-a₀))) := by
      have hS : Measurable (erlangPolynomial n) :=
        (continuous_iff_continuousAt.mpr (fun t => (erlangPolynomial_derivative n t).continuousAt)).measurable
      exact (((measurable_id.pow_const n).mul (measurable_const.mul measurable_id).exp).mul
        (hS.pow_const _)).ennreal_ofReal
    rw [← lintegral_const_mul _ hφ]
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr_ae
    have hz : ∀ᵐ t : ℝ, t ≠ 0 := by
      apply ae_iff.mpr
      simp
    filter_upwards [hz] with t ht0
    simp only [Pi.mul_apply]
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht)]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(n.factorial:ℝ))]
      exact erlang_pooled_integrand n a₀ c t ht
    · rw [indicator_of_not_mem (show t ∉ Ioi (0:ℝ) from ht)]
      have htn : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
      rw [gammaPDF_of_neg htn,zero_mul]
  · exact ((measurable_const.mul measurable_id).exp.mul
      ((measurable_const.sub (monotone_cdf _).measurable).pow_const _)).ennreal_ofReal

end RepeatedEvidenceProbability
