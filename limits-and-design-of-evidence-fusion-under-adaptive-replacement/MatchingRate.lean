import TensorTilt
import LikelihoodRate
import UniversalGrowth

open scoped BigOperators NNReal ENNReal Topology
open Set Finset MeasureTheory ProbabilityTheory Filter Function
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

def historyLikelihood {n : ℕ} (lam : ℝ) (x : Fin n → ℝ≥0) : ℝ :=
  ∏ i, (1-lam+lam*(x i : ℝ))

/-- Fixed-time validity against every independent, identically distributed
mean-constrained null. Universal conditional-null e-process validity includes
this subclass; the upper bound requires only this weaker condition. -/
def IIDNullValid (A : ∀ n : ℕ, (Fin n → ℝ≥0) → ℝ) : Prop :=
  ∀ (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ],
    Integrable (fun x : ℝ≥0 => (x : ℝ)) ρ → (∫ x : ℝ≥0, (x : ℝ) ∂ρ) ≤ 1 →
      ∀ n, Integrable (A n) (Measure.pi (fun _ : Fin n => ρ)) ∧
        (∫ x, A n x ∂Measure.pi (fun _ : Fin n => ρ)) ≤ 1

theorem tensor_tilt_ratio (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hint : Integrable (fun x : ℝ≥0 => Real.log (1+(x : ℝ))) ρ)
    (lam : ℝ) (hl : 0 < lam) (hl1 : lam < 1)
    (hmax : IsMaxOn (growthFunction (fun x : ℝ≥0 => (x : ℝ)) ρ) (Set.Ioo 0 1) lam)
    (A : ∀ n : ℕ, (Fin n → ℝ≥0) → ℝ) (hvalid : IIDNullValid A) (n : ℕ) :
    Integrable (fun x => A n x/historyLikelihood lam x) (Measure.pi (fun _ : Fin n => ρ)) ∧
      (∫ x, A n x/historyLikelihood lam x ∂Measure.pi (fun _ : Fin n => ρ)) ≤ 1 := by
  let X : ℝ≥0 → ℝ := fun x => x
  let d := fun x : ℝ≥0 => 1/(1-lam+lam*(x : ℝ))
  let P := reciprocalTilt ρ X lam
  have hXm : Measurable X := measurable_coe_nnreal_real
  obtain ⟨hP,hPi,hPm⟩ := interior_tilt_probability_mean_one X hXm
    (fun x => x.coe_nonneg) hint lam hl hl1 hmax
  letI : IsProbabilityMeasure P := hP
  have hD0 := interior_log_optimum_derivative_zero X hXm (fun x => x.coe_nonneg)
    hint lam hl hl1 hmax
  have hdI := (general_tilt_identities X (fun x => x.coe_nonneg) lam hl.le hl1 hD0.1 hD0.2).1
  have hd (x : ℝ≥0) : 0 ≤ d x := by
    apply div_nonneg (by norm_num)
    exact add_nonneg (sub_nonneg.mpr hl1.le) (mul_nonneg hl.le x.coe_nonneg)
  have hdm : Measurable d := measurable_const.div
    (measurable_const.add (measurable_const.mul measurable_coe_nnreal_real))
  letI : IsProbabilityMeasure (ρ.withDensity (fun x => ENNReal.ofReal (d x))) := hP
  have hpi := pi_withDensity (ι := Fin n) ρ d hd hdI
  have hav := hvalid P hPi hPm.le n
  change Integrable (A n) (Measure.pi (fun _ : Fin n => ρ.withDensity
    (fun x => ENNReal.ofReal (d x)))) ∧
      (∫ x, A n x ∂Measure.pi (fun _ : Fin n => ρ.withDensity
        (fun x => ENNReal.ofReal (d x)))) ≤ 1 at hav
  rw [hpi] at hav
  have hprod (x : Fin n → ℝ≥0) : 0 ≤ ∏ i, d (x i) := Finset.prod_nonneg (fun i _ => hd (x i))
  have hprodM : Measurable (fun x : Fin n → ℝ≥0 => ENNReal.ofReal (∏ i, d (x i))) :=
    (Finset.measurable_prod Finset.univ (fun i _ => hdm.comp (measurable_pi_apply i))).ennreal_ofReal
  have htop : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => ρ), ENNReal.ofReal (∏ i, d (x i)) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have he : (fun x : Fin n → ℝ≥0 => (ENNReal.ofReal (∏ i, d (x i))).toReal • A n x) =
      (fun x => A n x/historyLikelihood lam x) := by
    funext x
    rw [ENNReal.toReal_ofReal (hprod x),smul_eq_mul]
    simp only [d,one_div,historyLikelihood,div_eq_mul_inv,one_mul,Finset.prod_inv_distrib,mul_comm]
  constructor
  · rw [integrable_withDensity_iff_integrable_smul' hprodM htop,he] at hav
    exact hav.1
  · have hh := hav.2
    rw [integral_withDensity_eq_integral_toReal_smul hprodM htop (A n)] at hh
    change (∫ x, ((fun x : Fin n → ℝ≥0 =>
      (ENNReal.ofReal (∏ i, d (x i))).toReal • A n x) x) ∂Measure.pi (fun _ : Fin n => ρ)) ≤ 1 at hh
    rwa [he] at hh

variable {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem iid_history_law (X : ℕ → Ω → ℝ≥0) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (ρ : Measure ℝ≥0) (hmap : ∀ i, μ.map (X i)=ρ) (n : ℕ) :
    μ.map (fun ω (i : Fin n) => X i ω)=Measure.pi (fun _ : Fin n => ρ) := by
  have hh := (iIndepFun_iff_map_fun_eq_pi_map (fun i : Fin n => (hXm i).aemeasurable)).mp
    (hindep.precomp (g := fun i : Fin n => (i : ℕ)) Fin.val_injective)
  simpa only [hmap] using hh

/-- The full matching upper rate. The ratio moment bound is derived from the
interior tilt and finite-product change of measure, rather than assumed. -/
theorem matching_upper_rate (X : ℕ → Ω → ℝ≥0) (hXm : ∀ i, Measurable (X i))
    (hindep : iIndepFun X μ) (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hmap : ∀ i, μ.map (X i)=ρ)
    (hint : Integrable (fun x : ℝ≥0 => Real.log (1+(x : ℝ))) ρ)
    (lam : ℝ) (hl : 0 < lam) (hl1 : lam < 1)
    (hmax : IsMaxOn (growthFunction (fun x : ℝ≥0 => (x : ℝ)) ρ) (Set.Ico 0 1) lam)
    (A : ∀ n : ℕ, (Fin n → ℝ≥0) → ℝ) (hAm : ∀ n, Measurable (A n))
    (hAn : ∀ n x, 0 ≤ A n x) (hvalid : IIDNullValid A) :
    ∀ᵐ ω ∂μ, ∀ c : ℝ, growthFunction (fun x : ℝ≥0 => (x : ℝ)) ρ lam < c →
      ∀ᶠ n : ℕ in atTop, Real.log (A n (fun i => X i ω))/(n : ℝ) < c := by
  let f : ℝ≥0 → ℝ := fun x => Real.log (1-lam+lam*(x : ℝ))
  let M := fun n ω => historyLikelihood lam (fun i : Fin n => X i ω)
  let B := fun n ω => A n (fun i : Fin n => X i ω)
  have hfm : Measurable f := (measurable_const.add (measurable_const.mul measurable_coe_nnreal_real)).log
  have hfi := log_factor_integrable (fun x : ℝ≥0 => (x : ℝ)) measurable_coe_nnreal_real
    (fun x => x.coe_nonneg) hint lam hl.le hl1
  have hid (i : ℕ) : IdentDistrib (X i) (fun x : ℝ≥0 => x) μ ρ :=
    ⟨(hXm i).aemeasurable,measurable_id.aemeasurable,by simpa using hmap i⟩
  have hS := strong_law_ae_real (fun i ω => f (X i ω)) (((hid 0).comp hfm).symm.integrable_snd hfi)
    (fun i j hij => (hindep.indepFun hij).comp hfm hfm)
    (fun i => ((hid i).trans (hid 0).symm).comp hfm)
  have hInt : (∫ ω, f (X 0 ω) ∂μ) = growthFunction (fun x : ℝ≥0 => (x : ℝ)) ρ lam :=
    ((hid 0).comp hfm).integral_eq
  have hMpos (n : ℕ) (ω : Ω) : 0 < M n ω := Finset.prod_pos (fun i _ =>
    add_pos_of_pos_of_nonneg (sub_pos.mpr hl1) (mul_nonneg hl.le (X i ω).coe_nonneg))
  have hlog : ∀ᵐ ω ∂μ, Tendsto (fun n => Real.log (M n ω)/(n : ℝ)) atTop
      (nhds (growthFunction (fun x : ℝ≥0 => (x : ℝ)) ρ lam)) := by
    filter_upwards [hS] with ω hω
    rw [hInt] at hω
    have he (n : ℕ) : Real.log (M n ω)=∑ i ∈ Finset.range n, f (X i ω) := by
      rw [show M n ω=∏ i : Fin n, (1-lam+lam*(X i ω : ℝ)) from rfl,Real.log_prod]
      · exact Fin.sum_univ_eq_sum_range (fun i => f (X i ω)) n
      · intro i _
        exact (add_pos_of_pos_of_nonneg (sub_pos.mpr hl1)
          (mul_nonneg hl.le (X i ω).coe_nonneg)).ne'
    simpa only [he] using hω
  have hr (n : ℕ) : Integrable (fun ω => B n ω/M n ω) μ ∧
      (∫ ω, B n ω/M n ω ∂μ) ≤ 1 := by
    have ht := tensor_tilt_ratio ρ hint lam hl hl1 (fun u hu => hmax ⟨hu.1.le,hu.2⟩) A hvalid n
    let H := fun ω (i : Fin n) => X i ω
    have hHm : Measurable H := measurable_pi_lambda _ (fun i => hXm i)
    have hLmeas : Measurable (historyLikelihood (n := n) lam) :=
      Finset.measurable_prod Finset.univ (fun i _ => measurable_const.add
        (measurable_const.mul (measurable_coe_nnreal_real.comp (measurable_pi_apply i))))
    have hRat := (hAm n).div hLmeas
    rw [← iid_history_law X hXm hindep ρ hmap n] at ht
    constructor
    · exact (integrable_map_measure hRat.aestronglyMeasurable hHm.aemeasurable).mp ht.1
    · have ht2 := ht.2
      rw [integral_map hHm.aemeasurable hRat.aestronglyMeasurable] at ht2
      exact ht2
  have hg : 0 ≤ growthFunction (fun x : ℝ≥0 => (x : ℝ)) ρ lam := by
    have hh := hmax (show (0 : ℝ) ∈ Set.Ico 0 1 by norm_num)
    simpa [growthFunction] using hh
  exact likelihood_upper_rate B M (fun n ω => hAn n _) hMpos
    (fun n => (hr n).1) (fun n => (hr n).2) _ hg hlog

end
end EvidenceFusion
