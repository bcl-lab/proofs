import MonotoneCompletion
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

open scoped BigOperators NNReal
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def largestSum (z : ι → ℝ) (r : ℕ) : ℝ :=
  (cardinalityAttacks r).sup' (cardinalityAttacks_nonempty r) (fun C => ∑ i ∈ C, z i)

def cleanLog (x : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, Real.log (1-lam+lam*x i)

theorem log_factor_split (b lam x : ℝ) (hb : 0 < b) (hl : 0 ≤ lam) (hx : 0 ≤ x) :
    Real.log (b+lam*x) = Real.log b + Real.log (1+lam*x/b) := by
  have he : b+lam*x = b*(1+lam*x/b) := by field_simp
  rw [he,Real.log_mul hb.ne' (by positivity : 1+lam*x/b ≠ 0)]

theorem robustProduct_positive (b lam y : ι → ℝ)
    (A : Finset (Finset ι)) (hA : A.Nonempty)
    (hb : ∀ i, 0 < b i) (hl : ∀ i, 0 ≤ lam i) (hy : ∀ i, 0 ≤ y i) :
    0 < robustProduct b lam y A hA := by
  obtain ⟨C,hC,he⟩ := Finset.exists_mem_eq_inf' hA
    (fun C => ∏ i, if i ∈ C then b i else b i+lam i*y i)
  unfold robustProduct
  rw [he]
  apply Finset.prod_pos
  intro i _
  by_cases hi : i ∈ C
  · simpa [hi] using hb i
  · simp only [hi,if_false]
    exact add_pos_of_pos_of_nonneg (hb i) (mul_nonneg (hl i) (hy i))

/-- The exact logarithmic cost for a specified erased set. -/
theorem log_erased_product (b lam : ℝ) (hb : 0 < b) (hl : 0 ≤ lam)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (C : Finset ι) :
    Real.log (∏ i, if i ∈ C then b else b+lam*x i) =
      (∑ i, Real.log (b+lam*x i)) - ∑ i ∈ C, Real.log (1+lam*x i/b) := by
  rw [Real.log_prod]
  · have he (i : ι) : Real.log (if i ∈ C then b else b+lam*x i) =
        Real.log (b+lam*x i) - if i ∈ C then Real.log (1+lam*x i/b) else 0 := by
      by_cases hi : i ∈ C
      · simp only [hi,if_true]
        rw [log_factor_split b lam (x i) hb hl (hx i)]
        ring
      · simp [hi]
    simp_rw [he]
    rw [Finset.sum_sub_distrib]
    congr 1
    simp
  · intro i _
    by_cases hi : i ∈ C
    · simpa [hi] using hb.ne'
    · simp only [hi,if_false]
      exact (add_pos_of_pos_of_nonneg hb (mul_nonneg hl (hx i))).ne'

/-- Lemma S6's logarithmic loss bound. `largestSum` is the maximum sum
over at most r coordinates, avoiding any tie-breaking convention for sorting. -/
theorem replacement_log_loss (k : ℕ) (lam : ℝ) (hl : 0 ≤ lam) (hl1 : lam < 1)
    (x y : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hattack : hamming x y ≤ k) :
    cleanLog x lam - largestSum (fun i => Real.log (1+lam*x i/(1-lam))) (2*k) ≤
      Real.log (robustProduct (fun _ => 1-lam) (fun _ => lam) y
        (cardinalityAttacks k) (cardinalityAttacks_nonempty k)) := by
  let D := differences x y
  have hD : D.card ≤ k := hattack
  obtain ⟨C,hC,hmin⟩ := Finset.exists_mem_eq_inf' (cardinalityAttacks_nonempty k)
    (fun C => ∏ i, if i ∈ C then 1-lam else 1-lam+lam*y i)
  have hCk := (mem_cardinalityAttacks k C).mp hC
  have hU : (C ∪ D).card ≤ 2*k := by
    have hh := Finset.card_union_le C D
    omega
  have hp : (∏ i, if i ∈ C ∪ D then 1-lam else 1-lam+lam*x i) ≤
      ∏ i, if i ∈ C then 1-lam else 1-lam+lam*y i := by
    apply Finset.prod_le_prod
    · intro i _
      split_ifs
      · linarith
      · exact add_nonneg (by linarith) (mul_nonneg hl (hx i))
    · intro i _
      by_cases hiC : i ∈ C
      · simp [hiC]
      · by_cases hiD : i ∈ D
        · simp only [Finset.mem_union,hiC,hiD,or_true,if_true,if_false]
          exact le_add_of_nonneg_right (mul_nonneg hl (hy i))
        · have he : x i = y i := by simpa [D,differences] using hiD
          simp [hiC,hiD,he]
  have hpos : 0 < ∏ i, if i ∈ C ∪ D then 1-lam else 1-lam+lam*x i := by
    apply Finset.prod_pos
    intro i _
    split_ifs
    · linarith
    · exact add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg hl (hx i))
  have hh := Real.log_le_log hpos hp
  rw [log_erased_product (1-lam) lam (by linarith) hl x hx (C ∪ D)] at hh
  have hsum : (∑ i ∈ C ∪ D, Real.log (1+lam*x i/(1-lam))) ≤
      largestSum (fun i => Real.log (1+lam*x i/(1-lam))) (2*k) :=
    Finset.le_sup' (fun B => ∑ i ∈ B, Real.log (1+lam*x i/(1-lam)))
      ((mem_cardinalityAttacks (2*k) _).mpr hU)
  change cleanLog x lam - _ ≤ Real.log ((cardinalityAttacks k).inf'
    (cardinalityAttacks_nonempty k) (fun C => ∏ i, if i ∈ C then 1-lam else 1-lam+lam*y i))
  rw [hmin]
  dsimp [cleanLog]
  linarith

theorem log_factor_hasDerivAt (x lam : ℝ) (hx : 0 ≤ x) (hl : 0 ≤ lam) (hl1 : lam < 1) :
    HasDerivAt (fun t => Real.log (1-t+t*x)) ((x-1)/(1-lam+lam*x)) lam := by
  have hh := ((hasDerivAt_const lam (1 : ℝ)).sub (hasDerivAt_id lam)).add
    ((hasDerivAt_id lam).mul_const x)
  have hp : 0 < 1-lam+lam*x := add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg hl hx)
  simpa [sub_eq_add_neg,add_comm] using hh.log hp.ne'

theorem log_factor_lipschitz (x eps u v : ℝ) (hx : 0 ≤ x) (heps : 0 < eps)
    (hu : u ∈ Set.Icc eps (1-eps)) (hv : v ∈ Set.Icc eps (1-eps)) :
    |Real.log (1-v+v*x)-Real.log (1-u+u*x)| ≤ (1/eps)*|v-u| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (ht : t ∈ Set.Icc eps (1-eps)) =>
      (log_factor_hasDerivAt x t hx (by linarith [ht.1]) (by linarith [ht.2])).hasDerivWithinAt)
    (fun t (ht : t ∈ Set.Icc eps (1-eps)) => show
      ‖(x-1)/(1-t+t*x)‖ ≤ 1/eps by
        simpa [Real.norm_eq_abs,abs_div] using log_factor_derivative_bound x t eps hx heps ht.1 ht.2)
    (convex_Icc eps (1-eps)) hu hv
  simpa [Real.norm_eq_abs] using hh

theorem cleanLog_lipschitz (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (eps u v : ℝ) (heps : 0 < eps)
    (hu : u ∈ Set.Icc eps (1-eps)) (hv : v ∈ Set.Icc eps (1-eps)) :
    |cleanLog x v-cleanLog x u| ≤ (Fintype.card ι : ℝ)/eps*|v-u| := by
  unfold cleanLog
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (Real.log (1-v+v*x i)-Real.log (1-u+u*x i))| ≤
        ∑ i, |Real.log (1-v+v*x i)-Real.log (1-u+u*x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (1/eps)*|v-u| := Finset.sum_le_sum
      (fun i _ => log_factor_lipschitz (x i) eps u v (hx i) heps hu hv)
    _ = (Fintype.card ι : ℝ)/eps*|v-u| := by simp; ring

end
end EvidenceFusion
