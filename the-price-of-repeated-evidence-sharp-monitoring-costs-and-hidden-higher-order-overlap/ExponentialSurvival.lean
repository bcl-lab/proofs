import SurvivalMartingale
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
namespace RepeatedEvidenceProbability

/-- The rate-one exponential measure has the required exact survival mass. -/
theorem exponential_survival_mass (t : ℝ≥0) :
    (ProbabilityTheory.expMeasure 1).real (Ioi (t:ℝ)) = Real.exp (-(t:ℝ)) := by
  letI := ProbabilityTheory.isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have hc : (ProbabilityTheory.expMeasure 1).real (Iic (t:ℝ)) =
      1 - Real.exp (-(t:ℝ)) := by
    rw [← ProbabilityTheory.cdf_eq_real]
    change ProbabilityTheory.exponentialCDFReal 1 (t:ℝ) = _
    rw [ProbabilityTheory.exponentialCDFReal_eq (by norm_num), if_pos t.coe_nonneg]
    simp
  have h := measureReal_add_measureReal_compl (μ := ProbabilityTheory.expMeasure 1)
    (measurableSet_Iic (a := (t:ℝ)))
  rw [compl_Iic, measureReal_univ_eq_one, hc] at h
  linarith

noncomputable def exponentialSurvival (t : ℝ≥0) (z : ℝ) : ℝ :=
  (Ioi (t:ℝ)).indicator (fun _ => Real.exp (t:ℝ)) z

lemma exponentialSurvival_eq (t : ℝ≥0) :
    exponentialSurvival t = survivalProcess (ProbabilityTheory.expMeasure 1)
      (fun u : ℝ≥0 => Ioi (u:ℝ)) t := by
  funext z
  simp [exponentialSurvival, survivalProcess, exponential_survival_mass, Real.exp_neg]

/-- The paper's exponential survival process is a martingale in a concrete
survival filtration; the exponential distribution is instantiated, not assumed. -/
theorem exponential_survival_martingale :
    Martingale exponentialSurvival
      (survivalFiltration (fun t : ℝ≥0 => Ioi (t:ℝ))
        (fun _ _ h => Ioi_subset_Ioi h)) (ProbabilityTheory.expMeasure 1) := by
  letI := ProbabilityTheory.isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have he : exponentialSurvival = survivalProcess (ProbabilityTheory.expMeasure 1)
      (fun t : ℝ≥0 => Ioi (t:ℝ)) := funext exponentialSurvival_eq
  rw [he]
  exact survival_martingale _ _ _ (fun _ => measurableSet_Ioi)
    (fun t => by rw [exponential_survival_mass]; exact (Real.exp_pos _).ne')

theorem exponential_initial (z : ℝ) (hz : 0 < z) : exponentialSurvival 0 z = 1 := by
  simp [exponentialSurvival, hz]

/-- The continuous-time running supremum is exactly exp(z) for positive
survival times. The value at the death time itself is zero. -/
theorem exponential_running_supremum (z : ℝ) (hz : 0 < z) :
    (⨆ t : ℝ≥0, exponentialSurvival t z) = Real.exp z := by
  have hupper : ∀ t : ℝ≥0, exponentialSurvival t z ≤ Real.exp z := by
    intro t
    by_cases ht : (t:ℝ) < z
    · simp only [exponentialSurvival, indicator_of_mem (show z ∈ Ioi (t:ℝ) from ht)]
      exact (Real.exp_le_exp.mpr ht.le)
    · simp only [exponentialSurvival, indicator_of_not_mem (show z ∉ Ioi (t:ℝ) from ht)]
      exact (Real.exp_pos _).le
  have hb : BddAbove (Set.range (fun t : ℝ≥0 => exponentialSurvival t z)) :=
    ⟨Real.exp z, by rintro y ⟨t,rfl⟩; exact hupper t⟩
  apply le_antisymm (ciSup_le hupper)
  apply le_of_forall_lt
  intro b hbz
  by_cases hb1 : b < 1
  · exact hb1.trans_le (le_ciSup_of_le hb 0 (by rw [exponential_initial z hz]))
  · have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one (le_of_not_gt hb1)
    obtain ⟨t,hbt,htz⟩ := exists_between ((Real.log_lt_iff_lt_exp hbpos).2 hbz)
    have ht0 : 0 ≤ t := (Real.log_nonneg (le_of_not_gt hb1)).trans hbt.le
    apply lt_of_lt_of_le ((Real.log_lt_iff_lt_exp hbpos).1 hbt)
    apply le_ciSup_of_le hb (⟨t,ht0⟩ : ℝ≥0)
    change Real.exp t ≤ (Ioi t).indicator (fun _ : ℝ => Real.exp t) z
    rw [indicator_of_mem (show z ∈ Ioi t from htz)]

theorem exponential_positive_ae :
    ∀ᵐ z ∂ProbabilityTheory.expMeasure 1, (0:ℝ) < z := by
  letI := ProbabilityTheory.isProbabilityMeasureExponential (by norm_num : (0:ℝ) < 1)
  have hp : (ProbabilityTheory.expMeasure 1) (Ioi (0:ℝ)) = 1 := by
    apply (ENNReal.toReal_eq_one_iff _).1
    simpa using exponential_survival_mass 0
  exact (mem_ae_iff_prob_eq_one measurableSet_Ioi).2 hp

theorem exponential_initial_ae :
    ∀ᵐ z ∂ProbabilityTheory.expMeasure 1, exponentialSurvival 0 z = 1 := by
  filter_upwards [exponential_positive_ae] with z hz
  exact exponential_initial z hz

/-- Paths are right continuous, including at the time they fall to zero. -/
theorem exponential_survival_right_continuous (z : ℝ) (t : ℝ≥0) :
    ContinuousWithinAt (fun u => exponentialSurvival u z) (Ici t) t := by
  by_cases ht : (t:ℝ) < z
  · have he : ∀ᶠ u : ℝ≥0 in 𝓝 t, (u:ℝ) < z :=
      Filter.Tendsto.eventually_lt_const ht continuous_subtype_val.continuousAt
    have hc : ContinuousAt (fun u : ℝ≥0 => Real.exp (u:ℝ)) t :=
      Real.continuous_exp.continuousAt.comp continuous_subtype_val.continuousAt
    apply (hc.congr_of_eventuallyEq ?_).continuousWithinAt
    filter_upwards [he] with u hu
    exact indicator_of_mem hu _
  · apply (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ≥0 => (0:ℝ)) (Ici t) t).congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have hnot : ¬(u:ℝ) < z := not_lt.mpr ((le_of_not_gt ht).trans hu)
      exact indicator_of_not_mem (show z ∉ Ioi (u:ℝ) from hnot) _
    · exact mem_Ici.mpr le_rfl

/-- The critical exponential moment diverges as an extended-real integral. -/
theorem exponential_critical_moment_infinite :
    (∫⁻ z, ENNReal.ofReal (Real.exp z) ∂ProbabilityTheory.expMeasure 1) = ∞ := by
  change (∫⁻ z, ENNReal.ofReal (Real.exp z)
    ∂volume.withDensity (fun x : ℝ => ENNReal.ofReal (ProbabilityTheory.gammaPDFReal 1 1 x))) = ∞
  rw [lintegral_withDensity_eq_lintegral_mul volume
      (ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal
      Real.measurable_exp.ennreal_ofReal]
  change (∫⁻ z, ProbabilityTheory.exponentialPDF 1 z * ENNReal.ofReal (Real.exp z)) = ∞
  have he : (fun z => ProbabilityTheory.exponentialPDF 1 z * ENNReal.ofReal (Real.exp z)) =
      (Ici (0:ℝ)).indicator (fun _ => (1:ℝ≥0∞)) := by
    funext z
    by_cases hz : 0 ≤ z
    · rw [ProbabilityTheory.exponentialPDF_of_nonneg hz, indicator_of_mem (show z ∈ Ici (0:ℝ) from hz)]
      simp only [one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      simp
    · rw [ProbabilityTheory.exponentialPDF_of_neg (lt_of_not_ge hz), indicator_of_not_mem (show z ∉ Ici (0:ℝ) from hz)]
      simp
  rw [he,lintegral_indicator_const measurableSet_Ici]
  simp

/-- Every moment at or beyond load one diverges, including the boundary. -/
theorem exponential_supercritical_moment_infinite (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (p*z)) ∂ProbabilityTheory.expMeasure 1) = ∞ := by
  apply top_unique
  rw [← exponential_critical_moment_infinite]
  apply lintegral_mono_ae
  filter_upwards [exponential_positive_ae] with z hz
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  simpa using mul_le_mul_of_nonneg_right hp hz.le

/-- The actual running maximum of the constructed process has infinite moment
at every exponent at least one. -/
theorem exponential_running_maximum_moment_infinite (p : ℝ) (hp : 1 ≤ p) :
    (∫⁻ z, ENNReal.ofReal ((⨆ t : ℝ≥0, exponentialSurvival t z) ^ p)
      ∂ProbabilityTheory.expMeasure 1) = ∞ := by
  calc
    (∫⁻ z, ENNReal.ofReal ((⨆ t : ℝ≥0, exponentialSurvival t z) ^ p)
        ∂ProbabilityTheory.expMeasure 1) =
      ∫⁻ z, ENNReal.ofReal (Real.exp (p*z)) ∂ProbabilityTheory.expMeasure 1 := by
      apply lintegral_congr_ae
      filter_upwards [exponential_positive_ae] with z hz
      rw [exponential_running_supremum z hz, ← Real.exp_mul, mul_comm]
    _ = ∞ := exponential_supercritical_moment_infinite p hp

theorem exponential_tilt_density (p z : ℝ) :
    ProbabilityTheory.exponentialPDF 1 z * ENNReal.ofReal (Real.exp (p*z)) =
      (Ici (0:ℝ)).indicator (fun z => ENNReal.ofReal (Real.exp ((p-1)*z))) z := by
  by_cases hz : 0 ≤ z
  · rw [ProbabilityTheory.exponentialPDF_of_nonneg hz,indicator_of_mem (show z ∈ Ici (0:ℝ) from hz)]
    simp only [one_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  · rw [ProbabilityTheory.exponentialPDF_of_neg (lt_of_not_ge hz),indicator_of_not_mem (show z ∉ Ici (0:ℝ) from hz)]
    simp

/-- The exact finite moment on the other side of the load-one boundary. -/
theorem exponential_subcritical_moment (p : ℝ) (hp : p < 1) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (p*z)) ∂ProbabilityTheory.expMeasure 1) =
      ENNReal.ofReal (1/(1-p)) := by
  have hg : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (p*z))) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).ennreal_ofReal
  change (∫⁻ z, ENNReal.ofReal (Real.exp (p*z))
    ∂volume.withDensity (fun x : ℝ => ENNReal.ofReal (ProbabilityTheory.gammaPDFReal 1 1 x))) =
      ENNReal.ofReal (1/(1-p))
  rw [lintegral_withDensity_eq_lintegral_mul volume
      (ProbabilityTheory.measurable_gammaPDFReal 1 1).ennreal_ofReal
      hg]
  change (∫⁻ z, ProbabilityTheory.exponentialPDF 1 z * ENNReal.ofReal (Real.exp (p*z))) = _
  simp_rw [exponential_tilt_density]
  rw [lintegral_indicator measurableSet_Ici, ← restrict_Ioi_eq_restrict_Ici]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_mul_Ioi (sub_neg.mpr hp) 0)
    (ae_of_all _ (fun z => (Real.exp_pos ((p-1)*z)).le))]
  rw [integral_exp_mul_Ioi (sub_neg.mpr hp) 0]
  simp only [mul_zero,Real.exp_zero]
  apply congrArg ENNReal.ofReal
  field_simp [(sub_neg.mpr hp).ne, (sub_pos.mpr hp).ne']
  <;> ring

theorem exponential_running_maximum_subcritical_moment (p : ℝ) (hp : p < 1) :
    (∫⁻ z, ENNReal.ofReal ((⨆ t : ℝ≥0, exponentialSurvival t z) ^ p)
      ∂ProbabilityTheory.expMeasure 1) = ENNReal.ofReal (1/(1-p)) := by
  calc
    (∫⁻ z, ENNReal.ofReal ((⨆ t : ℝ≥0, exponentialSurvival t z) ^ p)
        ∂ProbabilityTheory.expMeasure 1) =
      ∫⁻ z, ENNReal.ofReal (Real.exp (p*z)) ∂ProbabilityTheory.expMeasure 1 := by
      apply lintegral_congr_ae
      filter_upwards [exponential_positive_ae] with z hz
      rw [exponential_running_supremum z hz, ← Real.exp_mul, mul_comm]
    _ = ENNReal.ofReal (1/(1-p)) := exponential_subcritical_moment p hp

end RepeatedEvidenceProbability
