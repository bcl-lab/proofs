import GammaConstruction
import OptimizedFinnerBound

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

theorem gammaStudySum_weighted_identity {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ω : V → ℝ) :
    (∑ i, a i * gammaStudySum A i ω) = ∑ v, sourceLoad A a v * ω v := by
  simp only [gammaStudySum,Finset.mul_sum,sourceLoad,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Exact expectation of the actual balanced gamma monitoring construction. -/
theorem balancedGammaModel_cost {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (q : V → ℝ)
    (hq : ∀ v, 0 ≤ q v) (hbalance : ∀ i, (∑ v, if A v i then q v else 0) = 1)
    (hload : ∀ v, sourceLoad A a v < 1) :
    (balancedGammaModel A q hq hbalance).cost a =
      ENNReal.ofReal (∏ v, (1-sourceLoad A a v)^(-q v)) := by
  letI : ∀ v, IsProbabilityMeasure (gammaShapeMeasure (q v)) := fun v => gammaShape_probability _ (hq v)
  let F (v : V) (z : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (sourceLoad A a v*z))
  have hF : ∀ v, Measurable (F v) := fun v =>
    (measurable_const.mul measurable_id).exp.ennreal_ofReal
  have hi : iIndepFun (fun v ω => F v (ω v)) (gammaProduct q) :=
    (probability_pi_coordinates_independent (fun v => gammaShapeMeasure (q v))).comp F hF
  have hpos : ∀ᵐ ω ∂gammaProduct q, ∀ i, 0 < gammaStudySum A i ω := by
    rw [ae_all_iff]
    intro i
    exact exponential_law_positive_ae _ _ (gammaStudySum_measurable A i)
      (gammaStudySum_law A q hq hbalance i)
  unfold MonitoringModel.cost
  change (∫⁻ ω, ∏ i, (balancedGammaModel A q hq hbalance).maximum i ω ^ a i
    ∂gammaProduct q) = _
  calc
    _ = ∫⁻ ω, ∏ v, F v (ω v) ∂gammaProduct q := by
      apply lintegral_congr_ae
      filter_upwards [hpos] with ω hω
      have hmax (i : I) : (balancedGammaModel A q hq hbalance).maximum i ω =
          ENNReal.ofReal (Real.exp (gammaStudySum A i ω)) := by
        change (⨆ t, ENNReal.ofReal (exponentialSurvival t (gammaStudySum A i ω))) = _
        rw [exponential_extended_maximum,if_pos (hω i)]
      simp_rw [hmax,ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),← Real.exp_mul]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),← Real.exp_sum]
      have he : (∑ i, gammaStudySum A i ω * a i) = ∑ v, sourceLoad A a v * ω v := by
        simpa only [mul_comm] using gammaStudySum_weighted_identity A a ω
      rw [he]
      simp only [F]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun v _ => (Real.exp_pos _).le),← Real.exp_sum]
    _ = ∏ v, ∫⁻ ω, F v (ω v) ∂gammaProduct q :=
      lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hi
        (fun v => (hF v).comp (measurable_pi_apply v))
    _ = ∏ v, ENNReal.ofReal ((1-sourceLoad A a v)^(-q v)) := by
      apply Finset.prod_congr rfl
      intro v _
      rw [← lintegral_map (hF v) (measurable_pi_apply v)]
      change (∫⁻ z, F v z ∂(Measure.pi (fun v => gammaShapeMeasure (q v))).map (fun ω => ω v)) = _
      rw [probability_pi_coordinate_law]
      exact gammaShape_exponential_moment _ _ (hq v) (hload v)
    _ = _ := (ENNReal.ofReal_prod_of_nonneg
      (fun v _ => (Real.rpow_pos_of_pos (sub_pos.mpr (hload v)) _).le)).symm

/-- Theorem 2: weighted gamma attainment of the actual universal cost. -/
theorem universalCost_weighted_gamma {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (q : V → ℝ) (L : ℝ)
    (ha : ∀ i, 0 < a i) (hq : ∀ v, 0 ≤ q v) (hL0 : 0 < L) (hL1 : L < 1)
    (hload : ∀ v, sourceLoad A a v ≤ L)
    (hbalance : ∀ i, (∑ v, if A v i then q v else 0) = 1)
    (hactive : ∀ v, 0 < q v → sourceLoad A a v = L) :
    universalCost A a = ENNReal.ofReal ((1-L)^(-((∑ i, a i)/L))) := by
  classical
  have hsum : (∑ i, a i)/L = ∑ v, q v := by
    apply RepeatedEvidence.balanced_exponent (fun v i => if A v i then 1 else 0) a q L
      hL0.ne' hq
    · intro i
      simpa only [ite_mul,one_mul,zero_mul] using hbalance i
    · intro v hv
      simpa only [RepeatedEvidence.load,ite_mul,one_mul,zero_mul,sourceLoad] using hactive v hv
  have hprod : (∏ v, (1-sourceLoad A a v)^(-q v)) = (1-L)^(-((∑ i, a i)/L)) := by
    have he (v : V) : (1-sourceLoad A a v)^(-q v) = (1-L)^(-q v) := by
      by_cases hv : q v = 0
      · simp [hv]
      · rw [hactive v (lt_of_le_of_ne (hq v) (Ne.symm hv))]
    simp_rw [he]
    rw [← Real.rpow_sum_of_pos (sub_pos.mpr hL1),Finset.sum_neg_distrib,hsum]
  apply le_antisymm
  · have h := universalCost_le_load_bound A a L ha hL0 hL1 hload
    simpa only [one_div,Real.inv_rpow (sub_pos.mpr hL1).le,
      Real.rpow_neg (sub_pos.mpr hL1).le] using h
  · have h := balancedGammaModel_cost A a q hq hbalance (fun v => (hload v).trans_lt hL1)
    rw [hprod] at h
    rw [← h]
    exact model_cost_le_universal _ a

theorem optimizedFinnerCost_le_load_bound {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (L : ℝ)
    (ha : ∀ i, 0 < a i) (hL0 : 0 < L) (hL1 : L < 1)
    (hload : ∀ v, sourceLoad A a v ≤ L) :
    optimizedFinnerCost A a ≤ ENNReal.ofReal ((1-L)^(-((∑ i, a i)/L))) := by
  have hscaled := RepeatedEvidence.scaled_fractional_matching
    (fun v i => if A v i then (1:ℝ) else 0) a L hL0 hL1 ha (fun v => by
      simpa only [RepeatedEvidence.load,sourceLoad,ite_mul,one_mul,zero_mul] using hload v)
  have hb : (fun i => a i/L) ∈ RepeatedEvidence.finnerDomain A a := by
    refine ⟨hscaled.1,?_⟩
    intro v
    simpa only [RepeatedEvidence.load,ite_mul,one_mul,zero_mul] using hscaled.2 v
  have h := iInf_le (fun b : {b // b ∈ RepeatedEvidence.finnerDomain A a} =>
    finnerBoundValue a b.val) ⟨fun i => a i/L,hb⟩
  change optimizedFinnerCost A a ≤ finnerBoundValue a (fun i => a i/L) at h
  have he : ∀ i, a i/(a i/L) = L := by intro i; field_simp [(ha i).ne',hL0.ne']
  unfold finnerBoundValue at h
  dsimp only at h
  simp_rw [he] at h
  have hC : 0 < 1/(1-L) := one_div_pos.mpr (sub_pos.mpr hL1)
  calc
    _ ≤ ∏ i, (ENNReal.ofReal (1/(1-L)))^(a i/L) := h
    _ = ENNReal.ofReal ((1/(1-L))^((∑ i, a i)/L)) := by
      simp_rw [ENNReal.ofReal_rpow_of_pos hC]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.rpow_pos_of_pos hC _).le),
        ← Real.rpow_sum_of_pos hC,← Finset.sum_div]
    _ = _ := by
      rw [one_div,Real.inv_rpow (sub_pos.mpr hL1).le,Real.rpow_neg (sub_pos.mpr hL1).le]

/-- Both universal cost and optimized Finner cost equal the attained value. -/
theorem weighted_gamma_attainment {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (q : V → ℝ) (L : ℝ)
    (ha : ∀ i, 0 < a i) (hq : ∀ v, 0 ≤ q v) (hL0 : 0 < L) (hL1 : L < 1)
    (hload : ∀ v, sourceLoad A a v ≤ L)
    (hbalance : ∀ i, (∑ v, if A v i then q v else 0) = 1)
    (hactive : ∀ v, 0 < q v → sourceLoad A a v = L) :
    universalCost A a = ENNReal.ofReal ((1-L)^(-((∑ i, a i)/L))) ∧
    optimizedFinnerCost A a = ENNReal.ofReal ((1-L)^(-((∑ i, a i)/L))) := by
  have h := universalCost_weighted_gamma A a q L ha hq hL0 hL1 hload hbalance hactive
  refine ⟨h,le_antisymm (optimizedFinnerCost_le_load_bound A a L ha hL0 hL1 hload) ?_⟩
  rw [← h]
  exact universalCost_le_optimizedFinnerCost A a ha

end RepeatedEvidenceProbability
