import HubAveraging
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option maxHeartbeats 3000000
namespace HubAveraging
noncomputable section
open Finset

/-- Cauchy--Schwarz in the exact form needed for a sum-preserving block. -/
theorem block_energy_floor {ι : Type*} (s : Finset ι) (y : ι → ℝ)
    (hs : 0 < s.card) :
    (∑ i ∈ s, y i)^2 / (s.card : ℝ) ≤ ∑ i ∈ s, (y i)^2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s y (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (div_le_iff₀ (by exact_mod_cast hs)).2 (by nlinarith)

/-- No update preserving the block sum can outperform exact local averaging. -/
theorem sum_preserving_block_bound {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) (hs : 0 < s.card)
    (hpres : ∑ i ∈ s, y i = ∑ i ∈ s, x i) :
    (∑ i ∈ s, (x i)^2) - (∑ i ∈ s, (y i)^2) ≤
      (∑ i ∈ s, (x i)^2) - (∑ i ∈ s, x i)^2 / (s.card : ℝ) := by
  have h := block_energy_floor s y hs
  rw [hpres] at h
  linarith

/-- The block variance of p plus signs and q minus signs. -/
theorem two_sign_variance (p q : ℝ) (hn : p+q ≠ 0) :
    p+q - (p-q)^2/(p+q) = 4*p*q/(p+q) := by
  field_simp
  ring

/-- Changing only a selected block changes global squared energy by exactly
its local squared-energy change. -/
theorem supported_energy_loss {ι : Type*} [Fintype ι]
    (s : Finset ι) (x y : ι → ℝ) (hoff : ∀ i, i ∉ s → x i = y i) :
    (∑ i, (x i)^2) - (∑ i, (y i)^2) =
      (∑ i ∈ s, (x i)^2) - (∑ i ∈ s, (y i)^2) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.subset_univ s)
  intro i _ hi
  rw [hoff i hi, sub_self]

/-- Proposition 5's geometric inequality, for a concrete finite block and
arbitrary real-valued output. The sign-count assumptions are explicit. -/
theorem concrete_cut_loss_bound {ι : Type*} [Fintype ι]
    (s : Finset ι) (x y : ι → ℝ) (p q : ℝ)
    (hs : 0 < s.card) (hc : (s.card : ℝ) = p+q)
    (hxsum : ∑ i ∈ s, x i = p-q)
    (hxsq : ∑ i ∈ s, (x i)^2 = p+q)
    (hpres : ∑ i ∈ s, y i = ∑ i ∈ s, x i)
    (hoff : ∀ i, i ∉ s → x i = y i) :
    (∑ i, (x i)^2) - (∑ i, (y i)^2) ≤ 4*p*q/(p+q) := by
  have hn : p+q ≠ 0 := by rw [← hc]; exact_mod_cast (Nat.ne_of_gt hs)
  have h := sum_preserving_block_bound s x y hs hpres
  rw [supported_energy_loss s x y hoff]
  simpa only [hxsum, hxsq, hc, two_sign_variance p q hn] using h

/-- The displayed coefficient in equation 15. -/
theorem closed_neighborhood_cut_constant (d k : ℝ) (hd : d+1 ≠ 0) :
    (k+1)+(d-k) - ((k+1)-(d-k))^2/((k+1)+(d-k)) =
      4*(k+1)*(d-k)/(d+1) := by
  have hden : (k+1)+(d-k) = d+1 := by ring
  rw [hden]
  field_simp
  ring

theorem cut_constant_le (d k : ℝ) (hd : 0 ≤ d) (_hk : 0 ≤ k) :
    4*(k+1)*(d-k)/(d+1) ≤ 4*(k+1) := by
  apply (div_le_iff₀ (by positivity : 0 < d+1)).2
  nlinarith [sq_nonneg (k+1)]

/-- Conversion from a common energy-loss cap to a residual ratio. -/
theorem cut_residual_ratio (N C E : ℝ) (hN : 0 < N)
    (hE : 0 ≤ E) (hcap : N-E ≤ C) :
    max 0 (1-C/N) ≤ E/N := by
  apply max_le
  · positivity
  · apply (le_div_iff₀ hN).2
    field_simp
    nlinarith

/-- One sweep captures b_d of the best possible local witness loss. -/
theorem local_solve_fraction (d : ℕ) (hd : 0 < d) :
    ((8 / 3 : ℝ)*(1-r d)) / (4*d/(d+1)) = b d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (d : ℝ)+1 ≠ 0 := by positivity
  unfold b beta
  field_simp
  ring

/-- Scalar aggregation of equation 8 into the quadratic loss formula.
The graph identities for S and H are explicit hypotheses. -/
theorem loss_polynomial_from_moments (d : ℕ) (hd : 0 < d)
    (S H Q R : ℝ) (hS : S = 2*Q-R/d)
    (hH : H = R/(d*(d+1))) :
    a d*S + b d*H = 2*a d*Q-gamma d*R := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hS, hH]
  unfold gamma
  field_simp
  ring

/-- Concavity means a quadratic's minimum over an interval is at an endpoint. -/
theorem concave_quadratic_endpoint (A g l u x : ℝ)
    (hg : 0 ≤ g) (hlx : l ≤ x) (hxu : x ≤ u) :
    min (2*A*l-g*l^2) (2*A*u-g*u^2) ≤ 2*A*x-g*x^2 := by
  by_cases hlu : l = u
  · have hx : x = l := by linarith
    simp [hlu, hx]
  · have hwidth : 0 < u-l := by
      rcases lt_or_eq_of_le (hlx.trans hxu) with h | h
      · linarith
      · exact False.elim (hlu h)
    have hxl : 0 ≤ x-l := sub_nonneg.mpr hlx
    have hux : 0 ≤ u-x := sub_nonneg.mpr hxu
    have hprod : 0 ≤ g*(x-l)*(u-x) := by positivity
    by_cases hends : 2*A*l-g*l^2 ≤ 2*A*u-g*u^2
    · rw [min_eq_left hends]
      have hfac : 0 ≤ (u-l)*(2*A-g*(u+l)) := by nlinarith
      have hslope : 0 ≤ 2*A-g*(u+l) := nonneg_of_mul_nonneg_right hfac hwidth
      nlinarith [mul_nonneg (sub_nonneg.mpr hlx) hslope]
    · rw [min_eq_right (le_of_not_ge hends)]
      have hfac : (u-l)*(2*A-g*(u+l)) ≤ 0 := by nlinarith
      have hslope : 2*A-g*(u+l) ≤ 0 := nonpos_of_mul_nonpos_right hfac hwidth
      nlinarith [mul_nonneg (sub_nonneg.mpr hxu) (neg_nonneg.mpr hslope)]

/-- The exponential part of equation 13, with its domain made explicit. -/
theorem independent_budget_exponential (t : ℝ) (d : ℕ)
    (ht : t ≤ 1) : (1-t)^d ≤ Real.exp (-(d : ℝ)*t) := by
  have hb : 1-t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1-t) hb d
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

/-- The exact concavity estimate used in equation 14. -/
theorem exponential_chord (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) :
    2*(1-Real.exp (-(1/2 : ℝ)))*t ≤ 1-Real.exp (-t) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-(1/2 : ℝ)))
    (show 0 ≤ 1-2*t by linarith) (show 0 ≤ 2*t by linarith)
    (show (1-2*t)+2*t=1 by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have he : 2*t*(-(1/2 : ℝ)) = -t := by ring
  rw [he] at h
  nlinarith

/-- Exact rational certificate for the advertised 147.6 comparison.
This is arithmetic on the two stated bounds, not a verification of the
independent-edge stochastic process or its graph spectral gap. -/
theorem benchmark_500_exact :
    (1476 / 10 : ℚ) * (1/375) < 1-(999/1000 : ℚ)^500 := by
  norm_num

/-- The second inequality in equation 14, for all parameters in its stated range. -/
theorem separation_ratio_bound (N lambda R : ℝ)
    (hN : 0 < N) (hl : 0 < lambda) (hr : 0 ≤ R)
    (hhalf : lambda/N ≤ 1/2) :
    8*(1-R)/(3*N*(1-Real.exp (-(lambda/N)))) ≤
      4/(3*(1-Real.exp (-(1/2 : ℝ)))*lambda) := by
  have ht : 0 < lambda/N := div_pos hl hN
  have hc : 0 < 1-Real.exp (-(1/2 : ℝ)) := by
    have he := Real.exp_lt_exp.mpr (show -(1/2 : ℝ) < 0 by norm_num)
    simp only [Real.exp_zero] at he
    linarith
  have he : 0 < 1-Real.exp (-(lambda/N)) := by
    have hh := Real.exp_lt_exp.mpr (show -(lambda/N) < 0 by linarith)
    simp only [Real.exp_zero] at hh
    linarith
  have hchord := exponential_chord (lambda/N) ht.le hhalf
  calc
    _ ≤ 8/(3*N*(1-Real.exp (-(lambda/N)))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    _ ≤ 8/(3*N*(2*(1-Real.exp (-(1/2 : ℝ)))*(lambda/N))) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left hchord (by positivity)
    _ = _ := by
      generalize hconst : 1-Real.exp (-(1/2 : ℝ)) = c at *
      have hc0 : c ≠ 0 := ne_of_gt hc
      field_simp [ne_of_gt hN, ne_of_gt hl, hc0]
      ring

/-- The degree-500 hub formula is bounded by exactly one over 375. -/
theorem hub_progress_500_upper :
    ((8/3 : ℝ)*(1-r 500))/1000 ≤ (1/375 : ℝ) := by
  have hr := r_nonneg 500
  linarith

theorem benchmark_500_real :
    (1476 / 10 : ℝ) * (1/375) < 1-(999/1000 : ℝ)^500 := by
  have h := (Rat.cast_lt (K := ℝ)).2 benchmark_500_exact
  push_cast at h
  exact h

theorem benchmark_500_combined :
    (1476/10 : ℝ)*(((8/3 : ℝ)*(1-r 500))/1000) < 1-(999/1000 : ℝ)^500 := by
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hub_progress_500_upper (by norm_num)) benchmark_500_real

end
end HubAveraging
