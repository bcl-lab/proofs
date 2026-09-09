import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Choose
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic

namespace Fusion
open Finset

/-- Pointwise form of Supplementary Equation S1. -/
theorem contrast_bounds (a b la ua lb ub : ℝ)
    (ha : la ≤ a ∧ a ≤ ua) (hb : lb ≤ b ∧ b ≤ ub) :
    la - ub ≤ a - b ∧ a - b ≤ ua - lb := by
  constructor <;> linarith

/-- Attained paired endpoints lie within the separate interval on the same set. -/
theorem attained_contrast_bounds {X : Type*} (Y : Set X) (a b : X → ℝ)
    (la ua lb ub L U : ℝ) (xlo xhi : X)
    (hlo : xlo ∈ Y) (hhi : xhi ∈ Y)
    (ha : ∀ x ∈ Y, la ≤ a x ∧ a x ≤ ua)
    (hb : ∀ x ∈ Y, lb ≤ b x ∧ b x ≤ ub)
    (hL : L = a xlo - b xlo) (hU : U = a xhi - b xhi) :
    la - ub ≤ L ∧ U ≤ ua - lb := by
  subst L; subst U
  exact ⟨(contrast_bounds _ _ _ _ _ _ (ha _ hlo) (hb _ hlo)).1,
    (contrast_bounds _ _ _ _ _ _ (ha _ hhi) (hb _ hhi)).2⟩

/-- Removing feasible outcomes cannot widen any valid interval. -/
theorem restrict_bounds {X : Type*} (Y Z : Set X) (f : X → ℝ) (L U : ℝ)
    (hsub : Z ⊆ Y) (h : ∀ x ∈ Y, L ≤ f x ∧ f x ≤ U) :
    ∀ x ∈ Z, L ≤ f x ∧ f x ≤ U := by
  intro x hx; exact h x (hsub hx)

/-- Equation 2 after each area is written in the standard rank-sum form. -/
theorem rank_contrast_identity {n : ℕ} (rA rB y : Fin n → ℝ) (offset D : ℝ) :
    ((∑ i, rA i * y i) - offset) / D -
      ((∑ i, rB i * y i) - offset) / D =
    (∑ i, (rA i - rB i) * y i) / D := by
  rw [← sub_div]
  congr 1
  simp only [sub_mul, sum_sub_distrib]
  ring

/-- Equation 3 holds pointwise even before restricting outcomes to binary values. -/
theorem brier_pointwise (pA pB y : ℝ) :
    (pB-y)^2 - (pA-y)^2 = pB^2-pA^2 + 2*(pA-pB)*y := by ring

theorem brier_sum {n : ℕ} (pA pB y : Fin n → ℝ) :
    (∑ i, ((pB i-y i)^2 - (pA i-y i)^2)) =
    (∑ i : Fin n, ((pB i)^2-(pA i)^2)) + ∑ i : Fin n, 2*(pA i-pB i)*y i := by
  simp_rw [brier_pointwise, sum_add_distrib]

/-- Equation 4, with h the difference of the two treatment indicators. -/
theorem net_benefit_pointwise (a b y w : ℝ) :
    (a*y-w*a*(1-y)) - (b*y-w*b*(1-y)) =
    (1+w)*(a-b)*y - w*(a-b) := by ring

theorem positive_denominator (N M : ℝ) (hM : 0 < M) (hN : M < N) :
    0 < M*(N-M) := mul_pos hM (sub_pos.mpr hN)

/-- Genuine positive-margin certification, conditional on interval validity. -/
theorem margin_certificate (L U t d : ℝ) (ht : L ≤ t ∧ t ≤ U)
    (h : d < L ∨ U < -d) : d < t ∨ t < -d := by
  rcases h with h | h
  · exact Or.inl (lt_of_lt_of_le h ht.1)
  · exact Or.inr (lt_of_le_of_lt ht.2 h)

theorem certificate_inclusion (L U l u d : ℝ)
    (h : L ≤ l ∧ u ≤ U) :
    (d < L ∨ U < -d) → (d < l ∨ u < -d) := by
  intro hc; rcases hc with hc | hc
  · exact Or.inl (lt_of_lt_of_le hc h.1)
  · exact Or.inr (lt_of_le_of_lt h.2 hc)

theorem margin_monotone (L U d e : ℝ) (h : d ≤ e) :
    (e < L ∨ U < -e) → (d < L ∨ U < -d) := by
  intro hc; rcases hc with hc | hc
  · exact Or.inl (lt_of_le_of_lt h hc)
  · exact Or.inr (lt_of_lt_of_le hc (neg_le_neg h))

/-- Numeric interpretation of the main decision count. -/
theorem unresolved_reduction : ((16:ℚ)-11)/16 = 5/16 := by norm_num


/-- Converts a numerator difference to the paper's positive-denominator scale. -/
theorem scaled_target_difference (C x y D : ℝ) (hD : 0 < D) :
    D*((C+x)/D-(C+y)/D)=x-y := by
  have hx := div_mul_cancel₀ (C+x) (ne_of_gt hD)
  have hy := div_mul_cancel₀ (C+y) (ne_of_gt hD)
  nlinarith

/-- An absolute numerator bound yields the scaled endpoint-width bound. -/
theorem scaled_width_bound (C x y D B : ℝ) (hD : 0 < D) (h : |x-y| ≤ B) :
    D*((C+x)/D-(C+y)/D) ≤ B := by
  rw [scaled_target_difference C x y D hD]
  exact le_trans (le_abs_self _) h

end Fusion
