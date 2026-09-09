import LogLoss

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem largestSum_mono (z v : ι → ℝ) (r : ℕ) (h : ∀ i, z i ≤ v i) :
    largestSum z r ≤ largestSum v r := by
  apply Finset.sup'_le
  intro C hC
  exact (Finset.sum_le_sum (fun i _ => h i)).trans
    (Finset.le_sup' (fun B => ∑ i ∈ B, v i) hC)

theorem uniform_log_contribution_bound (x eps lam : ℝ) (hx : 0 ≤ x) (he : 0 < eps)
    (hl : lam ∈ Set.Icc eps (1-eps)) :
    Real.log (1+lam*x/(1-lam)) ≤ Real.log (1+(1-eps)/eps*x) := by
  have hden : 0 < 1-lam := by linarith [hl.2]
  have hln : 0 ≤ lam := by linarith [hl.1]
  have hr : lam/(1-lam) ≤ (1-eps)/eps := by
    apply (div_le_div_iff₀ hden he).mpr
    nlinarith [hl.2]
  apply Real.log_le_log (by positivity)
  have hh := mul_le_mul_of_nonneg_right hr hx
  simpa only [div_mul_eq_mul_div] using add_le_add_left hh 1

/-- Proposition S7, in the equivalent maximum-over-deletion-sets formulation
of the sum of largest log contributions. A positive lower prior weight q
can be the minimum of the finite grid weights. -/
theorem finite_grid_comparison (k : ℕ) (eps eta q : ℝ)
    (he : 0 < eps) (hehalf : eps < 1/2) (hq : 0 < q)
    (grid : Finset ℝ) (pi : ℝ → ℝ)
    (hgrid : ∀ l ∈ grid, l ∈ Set.Icc eps (1-eps))
    (hpi : ∀ l ∈ grid, q ≤ pi l)
    (hcover : ∀ u ∈ Set.Icc eps (1-eps), ∃ l ∈ grid, |l-u| ≤ eta)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hattack : hamming x y ≤ k) :
    sSup (cleanLog x '' Set.Icc eps (1-eps)) - (Fintype.card ι : ℝ)*eta/eps -
      largestSum (fun i => Real.log (1+(1-eps)/eps*x i)) (2*k) + Real.log q ≤
      Real.log (∑ l ∈ grid, pi l * robustProduct (fun _ => 1-l) (fun _ => l) y
        (cardinalityAttacks k) (cardinalityAttacks_nonempty k)) := by
  let R := fun l => robustProduct (fun _ : ι => 1-l) (fun _ => l) y
    (cardinalityAttacks k) (cardinalityAttacks_nonempty k)
  let V := ∑ l ∈ grid, pi l*R l
  let W := largestSum (fun i => Real.log (1+(1-eps)/eps*x i)) (2*k)
  let cost := (Fintype.card ι : ℝ)*eta/eps
  have hp (l : ℝ) (hlg : l ∈ grid) : 0 < R l := by
    have hl := hgrid l hlg
    apply robustProduct_positive _ _ y _ _ (fun _ => by linarith [hl.2])
      (fun _ => by linarith [hl.1]) hy
  have hb (u : ℝ) (hu : u ∈ Set.Icc eps (1-eps)) :
      cleanLog x u ≤ Real.log V + cost + W - Real.log q := by
    obtain ⟨l,hlg,hlu⟩ := hcover u hu
    have hl := hgrid l hlg
    have hl0 : 0 ≤ l := by linarith [hl.1]
    have hl1 : l < 1 := by linarith [hl.2]
    have hpp : 0 < pi l := hq.trans_le (hpi l hlg)
    have hterm : pi l*R l ≤ V :=
      Finset.single_le_sum (fun j hj => mul_nonneg (hq.trans_le (hpi j hj)).le (hp j hj).le) hlg
    have hv := Real.log_le_log (mul_pos hpp (hp l hlg)) hterm
    rw [Real.log_mul hpp.ne' (hp l hlg).ne'] at hv
    have hprior := Real.log_le_log hq (hpi l hlg)
    have hloss := replacement_log_loss k l hl0 hl1 x y hx hy hattack
    have hW := largestSum_mono (fun i => Real.log (1+l*x i/(1-l)))
      (fun i => Real.log (1+(1-eps)/eps*x i)) (2*k)
      (fun i => uniform_log_contribution_bound (x i) eps l (hx i) he hl)
    have hLip := cleanLog_lipschitz x hx eps u l he hu hl
    have hcost : (Fintype.card ι : ℝ)/eps*|l-u| ≤ cost := by
      have hh := mul_le_mul_of_nonneg_left hlu
        (by positivity : 0 ≤ (Fintype.card ι : ℝ)/eps)
      dsimp [cost]
      simpa only [div_mul_eq_mul_div] using hh
    have hdist := (abs_le.mp (hLip.trans hcost)).1
    change cleanLog x l - _ ≤ Real.log (R l) at hloss
    change _ ≤ W at hW
    linarith
  have hSne : (cleanLog x '' Set.Icc eps (1-eps)).Nonempty :=
    ⟨cleanLog x eps,eps,⟨le_rfl,by linarith⟩,rfl⟩
  have hs := csSup_le hSne (by
    rintro z ⟨u,hu,rfl⟩
    exact hb u hu)
  change sSup (cleanLog x '' Set.Icc eps (1-eps)) - cost - W + Real.log q ≤ Real.log V
  linarith

end
end EvidenceFusion
