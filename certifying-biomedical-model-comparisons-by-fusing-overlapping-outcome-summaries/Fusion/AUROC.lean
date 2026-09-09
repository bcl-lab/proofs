import Fusion.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace FusionAUROC
open Finset
variable {ι : Type*} [Fintype ι]

/-- Pairwise discrimination credit, with half credit for ties. -/
noncomputable def credit (a b : ℝ) : ℝ := if b<a then 1 else if a=b then 1/2 else 0

theorem credit_symmetry (a b : ℝ) : credit a b + credit b a = 1 := by
  rcases lt_trichotomy a b with h | h | h
  · simp [credit,h,not_lt.mpr h.le,ne_of_lt h,ne_of_gt h]
  · subst b; norm_num [credit]
  · simp [credit,h,not_lt.mpr h.le,ne_of_lt h,ne_of_gt h]

/-- Ascending midrank, expressed by strict-lower and tied-score counts. -/
noncomputable def midrank (score : ι → ℝ) (i : ι) : ℝ :=
  (∑ j, if score j < score i then (1:ℝ) else 0) +
    ((∑ j, if score j = score i then (1:ℝ) else 0) + 1)/2

theorem midrank_credit (score : ι → ℝ) (i : ι) :
    midrank score i = 1/2 + ∑ j, credit (score i) (score j) := by
  have he (j : ι) : credit (score i) (score j) =
      (if score j < score i then (1:ℝ) else 0) +
      (if score j = score i then (1:ℝ) else 0)/2 := by
    by_cases h : score j < score i
    · simp [credit,h,ne_of_lt h]
    · by_cases he : score j = score i
      · simp [credit,h,he]
      · simp [credit,h,he,Ne.symm he]
  simp only [he,sum_add_distrib,midrank,div_eq_mul_inv,← sum_mul]
  ring

/-- The within-positive pair credit is exactly one half of squared mass.
    The algebra even holds for real weights, hence for binary labels. -/
theorem within_positive_credit (score y : ι → ℝ) :
    (∑ i, ∑ j, credit (score i) (score j)*y i*y j) = (∑ i, y i)^2/2 := by
  let W := ∑ i, ∑ j, credit (score i) (score j)*y i*y j
  have hs : (∑ i, ∑ j, credit (score j) (score i)*y i*y j) = W := by
    rw [sum_comm]
    unfold W
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    ring
  have he : W+W = (∑ i, y i)*(∑ i, y i) := by
    conv_lhs => rhs; rw [← hs]
    unfold W
    rw [← sum_add_distrib]
    simp only [mul_sum,sum_mul]
    apply sum_congr rfl
    intro i hi
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    have hc := credit_symmetry (score i) (score j)
    calc
      _ = (credit (score i) (score j)+credit (score j) (score i))*y i*y j := by ring
      _ = _ := by rw [hc]; ring
  dsimp [W] at he ⊢
  nlinarith

/-- Standard area-under-curve rank-sum identity derived from the pairwise
    definition, including tied scores and arbitrary finite cohorts. -/
theorem pairwise_rank_sum (score y : ι → ℝ) :
    (∑ i, ∑ j, credit (score i) (score j)*y i*(1-y j)) =
      (∑ i, midrank score i*y i) - (∑ i, y i)*((∑ i, y i)+1)/2 := by
  have hr : (∑ i, midrank score i*y i) =
      (∑ i, y i)/2 + ∑ i, ∑ j, credit (score i) (score j)*y i := by
    simp only [midrank_credit,add_mul,sum_add_distrib,sum_mul]
    congr 1
    simp only [div_eq_mul_inv,sum_mul]
    apply sum_congr rfl; intro i hi; ring
  have hp : (∑ i, ∑ j, credit (score i) (score j)*y i*(1-y j)) =
      (∑ i, ∑ j, credit (score i) (score j)*y i) -
      (∑ i, ∑ j, credit (score i) (score j)*y i*y j) := by
    simp [mul_sub,sum_sub_distrib]
  rw [hp,within_positive_credit,hr]
  ring

/-- Paired area under the receiver operating characteristic curve contrast,
    directly from two pairwise definitions with half credit for tied scores. -/
theorem paired_area_contrast (scoreA scoreB y : ι → ℝ) (D : ℝ) :
    (∑ i, ∑ j, credit (scoreA i) (scoreA j)*y i*(1-y j))/D -
      (∑ i, ∑ j, credit (scoreB i) (scoreB j)*y i*(1-y j))/D =
      (∑ i, (midrank scoreA i-midrank scoreB i)*y i)/D := by
  rw [pairwise_rank_sum,pairwise_rank_sum,← sub_div]
  congr 1
  simp only [sub_mul,sum_sub_distrib]
  ring

end FusionAUROC
