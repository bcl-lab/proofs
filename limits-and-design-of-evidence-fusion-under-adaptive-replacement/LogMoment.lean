import SparseTrimming

open scoped BigOperators NNReal ENNReal Topology
open Finset Set MeasureTheory ProbabilityTheory Filter Function
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem log_factor_abs_bound (x lam : ℝ) (hx : 0 ≤ x) (hl : 0 ≤ lam) (hl1 : lam < 1) :
    |Real.log (1-lam+lam*x)| ≤ |Real.log (1-lam)| + Real.log (1+x) := by
  have hb : 0 < 1-lam := by linarith
  have hL : 0 < 1-lam+lam*x := add_pos_of_pos_of_nonneg hb (mul_nonneg hl hx)
  have hlo := Real.log_le_log hb (le_add_of_nonneg_right (mul_nonneg hl hx))
  have hhi := Real.log_le_log hL (show 1-lam+lam*x ≤ 1+x by
    nlinarith [mul_nonneg (le_of_lt hb) hx])
  have hlog : 0 ≤ Real.log (1+x) := Real.log_nonneg (by linarith)
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log (1-lam))],
    by linarith [abs_nonneg (Real.log (1-lam))]⟩

theorem log_factor_integrable (X : Ω → ℝ) (hXm : Measurable X) (hXn : ∀ ω, 0 ≤ X ω)
    (hint : Integrable (fun ω => Real.log (1+X ω)) μ)
    (lam : ℝ) (hl : 0 ≤ lam) (hl1 : lam < 1) :
    Integrable (fun ω => Real.log (1-lam+lam*X ω)) μ := by
  apply ((integrable_const |Real.log (1-lam)|).add hint).mono'
    ((measurable_const.add (measurable_const.mul hXm)).log.aestronglyMeasurable)
  filter_upwards [] with ω
  simpa [Real.norm_eq_abs] using log_factor_abs_bound (X ω) lam (hXn ω) hl hl1

theorem log_contribution_integrable (X : Ω → ℝ) (hXm : Measurable X) (hXn : ∀ ω, 0 ≤ X ω)
    (hint : Integrable (fun ω => Real.log (1+X ω)) μ)
    (lam : ℝ) (hl : 0 ≤ lam) (hl1 : lam < 1) :
    Integrable (fun ω => Real.log (1+lam*X ω/(1-lam))) μ := by
  have hh := (log_factor_integrable X hXm hXn hint lam hl hl1).sub
    (integrable_const (Real.log (1-lam)))
  have he : (fun ω => Real.log (1-lam+lam*X ω)-Real.log (1-lam)) =
      (fun ω => Real.log (1+lam*X ω/(1-lam))) := by
    funext ω
    rw [log_factor_split (1-lam) lam (X ω) (by linarith) hl (hXn ω)]
    ring
  change Integrable (fun ω => Real.log (1-lam+lam*X ω)-Real.log (1-lam)) μ at hh
  rwa [he] at hh

theorem expected_log_lipschitz (X : Ω → ℝ) (hXm : Measurable X)
    (hXn : ∀ ω, 0 ≤ X ω) (hint : Integrable (fun ω => Real.log (1+X ω)) μ)
    (eps u v : ℝ) (he : 0 < eps) (hu : u ∈ Set.Icc eps (1-eps))
    (hv : v ∈ Set.Icc eps (1-eps)) :
    |(∫ ω, Real.log (1-v+v*X ω) ∂μ) - (∫ ω, Real.log (1-u+u*X ω) ∂μ)| ≤
      (1/eps)*|v-u| := by
  have hiu := log_factor_integrable X hXm hXn hint u (by linarith [hu.1]) (by linarith [hu.2])
  have hiv := log_factor_integrable X hXm hXn hint v (by linarith [hv.1]) (by linarith [hv.2])
  rw [← integral_sub hiv hiu]
  have hh := norm_integral_le_of_norm_le_const (μ := μ)
    (Filter.Eventually.of_forall (fun ω => show
      ‖Real.log (1-v+v*X ω)-Real.log (1-u+u*X ω)‖ ≤ (1/eps)*|v-u| by
        simpa only [Real.norm_eq_abs] using log_factor_lipschitz (X ω) eps u v (hXn ω) he hu hv))
  simpa [Real.norm_eq_abs] using hh

/-- A fixed fraction achieves its clean log-growth rate uniformly over all
allowed observed vectors, under a vanishing count envelope. This uses the
actual strong law and the proved sparse-trimming limit. -/
theorem fixed_fraction_growth_ae (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXn : ∀ i ω, 0 ≤ X i ω)
    (hint : Integrable (fun ω => Real.log (1+X 0 ω)) μ)
    (hindep : Pairwise ((IndepFun · · μ) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (k : ℕ → ℕ) (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (nhds 0))
    (lam : ℝ) (hl : 0 ≤ lam) (hl1 : lam < 1) :
    ∀ᵐ ω ∂μ, ∀ c : ℝ, c < (∫ ω, Real.log (1-lam+lam*X 0 ω) ∂μ) →
      ∀ᶠ n : ℕ in atTop, ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) →
        hamming (fun i : Fin n => X i ω) y ≤ k n →
        c ≤ Real.log (robustProduct (fun _ => 1-lam) (fun _ => lam) y
          (cardinalityAttacks (k n)) (cardinalityAttacks_nonempty (k n)))/(n : ℝ) := by
  let f : ℝ → ℝ := fun x => Real.log (1-lam+lam*x)
  let z : ℝ → ℝ := fun x => Real.log (1+lam*x/(1-lam))
  have hfm : Measurable f := (measurable_const.add (measurable_const.mul measurable_id)).log
  have hzm : Measurable z := (measurable_const.add
    ((measurable_const.mul measurable_id).div_const (1-lam))).log
  have hfi := log_factor_integrable (X 0) (hXm 0) (hXn 0) hint lam hl hl1
  have hzi := log_contribution_integrable (X 0) (hXm 0) (hXn 0) hint lam hl hl1
  have hS := strong_law_ae_real (fun i ω => f (X i ω)) hfi
    (fun i j hij => (hindep hij).comp hfm hfm) (fun i => (hident i).comp hfm)
  have hk2 : Tendsto (fun n => ((2*k n : ℕ) : ℝ)/(n : ℝ)) atTop (nhds 0) := by
    simpa [Nat.cast_mul,mul_div_assoc] using hk.const_mul 2
  have hT := sparse_trimming_ae (fun i ω => z (X i ω)) hzi (fun i => hzm.comp (hXm i))
    (fun i ω => Real.log_nonneg (by
      have hp : 0 ≤ lam*X i ω/(1-lam) := div_nonneg (mul_nonneg hl (hXn i ω)) (by linarith)
      linarith))
    (fun i j hij => (hindep hij).comp hzm hzm) (fun i => (hident i).comp hzm)
    (fun n => 2*k n) hk2
  filter_upwards [hS,hT] with ω hS hT c hc
  have hh := hS.sub hT
  simp only [sub_zero] at hh
  have hev := hh.eventually (lt_mem_nhds hc)
  filter_upwards [hev] with n hn y hy ha
  have hbound := replacement_log_loss (k n) lam hl hl1 (fun i : Fin n => X i ω) y
    (fun i => hXn i ω) hy ha
  have he := Fin.sum_univ_eq_sum_range (fun i => f (X i ω)) n
  change (∑ i : Fin n, f (X i ω)) - _ ≤ _ at hbound
  rw [he] at hbound
  have hb := div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)
  rw [sub_div] at hb
  exact hn.le.trans hb

end
end EvidenceFusion
