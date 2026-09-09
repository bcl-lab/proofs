import LocalMGF
import GammaMoments

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

/-- The zero-shape limit is a point mass, as used by zero certificate weights. -/
noncomputable def gammaShapeMeasure (q : ℝ) : Measure ℝ :=
  if q = 0 then Measure.dirac 0 else gammaMeasure q 1

theorem gammaShape_probability (q : ℝ) (hq : 0 ≤ q) :
    IsProbabilityMeasure (gammaShapeMeasure q) := by
  unfold gammaShapeMeasure
  split_ifs with he
  · infer_instance
  · exact isProbabilityMeasureGamma (lt_of_le_of_ne hq (Ne.symm he)) (by norm_num)

theorem gammaShape_exponential_moment (q p : ℝ) (hq : 0 ≤ q) (hp : p < 1) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (p*z)) ∂gammaShapeMeasure q) =
      ENNReal.ofReal ((1-p)^(-q)) := by
  unfold gammaShapeMeasure
  split_ifs with he
  · simp [he]
  · exact gamma_subcritical_moment q p (lt_of_le_of_ne hq (Ne.symm he)) hp

theorem gammaShape_exponential_integrable (q p : ℝ) (hq : 0 ≤ q) (hp : p < 1) :
    Integrable (fun z => Real.exp (p*z)) (gammaShapeMeasure q) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)
    (ae_of_all _ (fun z => (Real.exp_pos _).le))).1
  simp only [id_eq]
  rw [gammaShape_exponential_moment q p hq hp]
  exact ENNReal.ofReal_ne_top

theorem gammaShape_mgf (q p : ℝ) (hq : 0 ≤ q) (hp : p < 1) :
    mgf id (gammaShapeMeasure q) p = (1-p)^(-q) := by
  unfold mgf
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun z => (Real.exp_pos _).le))
    ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)]
  change (∫⁻ z, ENNReal.ofReal (Real.exp (p*z)) ∂gammaShapeMeasure q).toReal = _
  rw [gammaShape_exponential_moment q p hq hp,ENNReal.toReal_ofReal]
  exact (Real.rpow_pos_of_pos (sub_pos.mpr hp) _).le

/-- A finite sum of independent gamma variables has the summed shape,
including zero shape coordinates. This is a law equality, not a moment
identity or a convolution hypothesis. -/
theorem independent_gamma_sum_law {I Ω : Type} [Fintype I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (G : I → Ω → ℝ) (q : I → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hG : ∀ i, Measurable (G i)) (hind : iIndepFun G μ)
    (hlaw : ∀ i, μ.map (G i) = gammaShapeMeasure (q i)) :
    μ.map (fun ω => ∑ i, G i ω) = gammaShapeMeasure (∑ i, q i) := by
  have hsumq : 0 ≤ ∑ i, q i := Finset.sum_nonneg (fun i _ => hq i)
  letI := gammaShape_probability (∑ i, q i) hsumq
  have hi (i : I) (t : ℝ) (ht : t < 1) : Integrable (fun ω => Real.exp (t*G i ω)) μ := by
    have h := gammaShape_exponential_integrable (q i) t (hq i) ht
    rw [← hlaw i] at h
    exact (integrable_map_measure ((measurable_const.mul measurable_id).exp.aestronglyMeasurable)
      (hG i).aemeasurable).1 h
  have hm (i : I) (t : ℝ) (ht : t < 1) : mgf (G i) μ t = (1-t)^(-q i) := by
    rw [← mgf_id_map (hG i).aemeasurable,hlaw i]
    exact gammaShape_mgf (q i) t (hq i) ht
  have h := law_eq_of_mgf_near_zero μ (gammaShapeMeasure (∑ i, q i))
    (fun ω => ∑ i, G i ω) id
    (Finset.univ.measurable_sum (fun i _ => hG i)) measurable_id (1/2) (by norm_num)
    (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · simpa using h
  · have ht1 : t < 1 := lt_trans ht.2 (by norm_num)
    simpa only [Finset.sum_apply] using hind.integrable_exp_mul_sum hG (fun i _ => hi i t ht1)
  · exact gammaShape_exponential_integrable _ t hsumq (lt_trans ht.2 (by norm_num))
  · have ht1 : t < 1 := lt_trans ht.2 (by norm_num)
    have hs := hind.mgf_sum hG Finset.univ (t := t)
    have he : (∑ i, G i) = fun ω => ∑ i, G i ω := by
      funext ω
      simp only [Finset.sum_apply]
    rw [he] at hs
    rw [hs,gammaShape_mgf _ t hsumq ht1]
    simp_rw [hm _ t ht1]
    rw [← Real.rpow_sum_of_pos (sub_pos.mpr ht1),Finset.sum_neg_distrib]

end RepeatedEvidenceProbability
