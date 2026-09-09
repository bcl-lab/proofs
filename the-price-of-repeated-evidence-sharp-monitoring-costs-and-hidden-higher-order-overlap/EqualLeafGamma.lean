import PooledExact

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

noncomputable def leafSum (J : Type) [Fintype J] (x : J → ℝ) : ℝ := ∑ j, x j

theorem leafSum_measurable (J : Type) [Fintype J] : Measurable (leafSum J) :=
  Finset.measurable_sum _ (fun j _ => measurable_pi_apply j)

theorem leafSum_gamma_law (J : Type) [Fintype J] :
    (exponentialProduct J).map (leafSum J) = gammaShapeMeasure (Fintype.card J) := by
  haveI := isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have h := independent_gamma_sum_law (exponentialProduct J) (fun j x => x j) (fun _ => (1:ℝ))
    (fun _ => zero_le_one) (fun j => measurable_pi_apply j)
    (probability_pi_coordinates_independent (fun _ : J => expMeasure 1)) (fun j => ?_)
  · simpa [leafSum] using h
  · simpa [gammaShapeMeasure,expMeasure] using
      probability_pi_coordinate_law (fun _ : J => expMeasure 1) j

theorem weightedSum_equal_leaves (J : Type) [Fintype J] (c : ℝ) (x : J → ℝ) :
    weightedSum (fun _ : J => c) x = c*leafSum J x := by
  simp only [weightedSum,leafSum,Finset.mul_sum]

theorem exponential_law_moment {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Ω → ℝ) (hE : Measurable E) (hlaw : μ.map E = expMeasure 1) (p : ℝ) (hp : p < 1) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (p*E ω)) ∂μ) = ENNReal.ofReal (1/(1-p)) := by
  have hm : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (p*z))) :=
    (measurable_const.mul measurable_id).exp.ennreal_ofReal
  have h := exponential_subcritical_moment p hp
  rw [← hlaw,lintegral_map hm hE] at h
  exact h

theorem leafSum_exponential_moment (J : Type) [Fintype J] (p : ℝ) (hp : p < 1) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (p*leafSum J x)) ∂exponentialProduct J) =
      ENNReal.ofReal ((1/(1-p))^(Fintype.card J : ℝ)) := by
  have hm : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (p*z))) :=
    (measurable_const.mul measurable_id).exp.ennreal_ofReal
  have h := gammaShape_exponential_moment (Fintype.card J) p (Nat.cast_nonneg _) hp
  rw [← leafSum_gamma_law J,lintegral_map hm (leafSum_measurable J)] at h
  rw [Real.rpow_neg (sub_pos.mpr hp).le,← Real.inv_rpow (sub_pos.mpr hp).le] at h
  simpa only [one_div] using h

theorem pooled_equal_leaf_cost_integral (J : Type) [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ c : ℝ) (ha₀ : 0 < a₀) (hc : 0 < c) :
    universalCost pooledUses (pooledPowers a₀ (fun _ : J => c)) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (a₀*pooledSurvivalTime (fun _ : J => c) x+c*leafSum J x))
        ∂exponentialProduct J := by
  rw [pooled_exact_cost a₀ _ ha₀ (fun _ => hc),
    ← pooledAttainingModel_cost a₀ _ (fun _ => hc.ne'),pooledAttainingModel,survivalModel_cost]
  apply lintegral_congr
  intro x
  congr 2
  simp [Fintype.sum_option,pooledPowers,pooledTimes,leafSum,Finset.mul_sum]

end RepeatedEvidenceProbability
