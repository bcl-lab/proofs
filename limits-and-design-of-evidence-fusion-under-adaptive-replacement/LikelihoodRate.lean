import InteriorTilt
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

open scoped BigOperators ENNReal Topology
open Set MeasureTheory ProbabilityTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exponential_crossing_bound (A M : Ω → ℝ) (hA : ∀ ω, 0 ≤ A ω)
    (hM : ∀ ω, 0 < M ω) (hi : Integrable (fun ω => A ω/M ω) μ)
    (hmean : (∫ ω, A ω/M ω ∂μ) ≤ 1) (t : ℝ) :
    μ {ω | Real.exp t ≤ A ω/M ω} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  have hh := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => div_nonneg (hA ω) (hM ω).le)) hi (Real.exp t)
  have hb : μ.real {ω | Real.exp t ≤ A ω/M ω} ≤ Real.exp (-t) := by
    have h := (le_div_iff₀ (Real.exp_pos t)).mpr (show
      μ.real {ω | Real.exp t ≤ A ω/M ω} * Real.exp t ≤ 1 by nlinarith)
    simpa [Real.exp_neg,one_div] using h
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | Real.exp t ≤ A ω/M ω})]
  exact ENNReal.ofReal_le_ofReal hb

theorem likelihood_ratio_subexponential (A M : ℕ → Ω → ℝ)
    (hA : ∀ n ω, 0 ≤ A n ω) (hM : ∀ n ω, 0 < M n ω)
    (hi : ∀ n, Integrable (fun ω => A n ω/M n ω) μ)
    (hmean : ∀ n, (∫ ω, A n ω/M n ω ∂μ) ≤ 1)
    (delta : ℝ) (hd : 0 < delta) :
    ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, A n ω/M n ω < Real.exp (delta*n) := by
  have hs : Summable (fun n : ℕ => Real.exp (-(delta*n))) := by
    have hh := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hd)
    simpa [mul_comm] using hh
  have hfinite : (∑' n : ℕ, ENNReal.ofReal (Real.exp (-(delta*n)))) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) hs]
    exact ENNReal.ofReal_ne_top
  have hprob : (∑' n : ℕ, μ {ω | Real.exp (delta*n) ≤ A n ω/M n ω}) ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (ENNReal.tsum_le_tsum (fun n =>
      exponential_crossing_bound (A n) (M n) (hA n) (hM n) (hi n) (hmean n) (delta*n)))
  have hh := ae_eventually_not_mem hprob
  simpa only [Set.mem_setOf_eq,not_le] using hh

/-- The Borel-Cantelli and likelihood-ratio part of S9. Zero evidence values
are handled explicitly, so Lean's real log at zero creates no false rate claim. -/
theorem likelihood_upper_rate (A M : ℕ → Ω → ℝ)
    (hA : ∀ n ω, 0 ≤ A n ω) (hM : ∀ n ω, 0 < M n ω)
    (hi : ∀ n, Integrable (fun ω => A n ω/M n ω) μ)
    (hmean : ∀ n, (∫ ω, A n ω/M n ω ∂μ) ≤ 1)
    (g : ℝ) (hg : 0 ≤ g)
    (hlog : ∀ᵐ ω ∂μ, Tendsto (fun n => Real.log (M n ω)/(n : ℝ)) atTop (nhds g)) :
    ∀ᵐ ω ∂μ, ∀ c : ℝ, g < c →
      ∀ᶠ n : ℕ in atTop, Real.log (A n ω)/(n : ℝ) < c := by
  have hb (j : ℕ) := likelihood_ratio_subexponential A M hA hM hi hmean
    (1/(j+1 : ℝ)) (by positivity)
  have hall := (ae_all_iff).mpr hb
  filter_upwards [hall,hlog] with ω hω hL c hc
  have heps : 0 < (c-g)/2 := by linarith
  obtain ⟨j,hj⟩ := exists_nat_gt (1/((c-g)/2))
  have hjp : 0 < (j+1 : ℝ) := by positivity
  have hd : 1/(j+1 : ℝ) < (c-g)/2 := by
    apply (div_lt_iff₀ hjp).mpr
    have hh := (div_lt_iff₀ heps).mp hj
    nlinarith
  have hLimit := hL.eventually (gt_mem_nhds (show g < g+(c-g)/2 by linarith))
  filter_upwards [hω j,hLimit,eventually_gt_atTop 0] with n hn hLn hn0
  by_cases hAz : A n ω = 0
  · simp [hAz,show 0 < c from hg.trans_lt hc]
  · have hAp : 0 < A n ω := lt_of_le_of_ne (hA n ω) (Ne.symm hAz)
    have hratio : 0 < A n ω/M n ω := div_pos hAp (hM n ω)
    have hlogs := Real.log_lt_log hratio hn
    rw [Real.log_div hAz (hM n ω).ne',Real.log_exp] at hlogs
    have hnp : (0 : ℝ) < n := by exact_mod_cast hn0
    have hdiv := (div_lt_div_of_pos_right hlogs hnp)
    rw [sub_div,mul_div_cancel_right₀ _ hnp.ne'] at hdiv
    linarith

end
end EvidenceFusion
