import FinnerMonitoring
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem weighted_geometric_strict (b x y : ℝ) (hb : 0 < b) (hb1 : b < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hne : x ≠ y) :
    x^b*y^(1-b) < b*x+(1-b)*y := by
  let w : Bool → ℝ := fun v => if v then b else 1-b
  let z : Bool → ℝ := fun v => if v then x else y
  have hw : ∀ v ∈ (Finset.univ : Finset Bool), 0 < w v := by
    intro v _; cases v <;> dsimp [w] <;> linarith
  have hws : ∑ v : Bool, w v = 1 := by simp [w,Fintype.sum_bool]
  have hz : ∀ v ∈ (Finset.univ : Finset Bool), 0 ≤ z v := by
    intro v _; cases v <;> assumption
  have h := (Real.geom_mean_lt_arith_mean_weighted_iff_of_pos Finset.univ w z hw hws hz).mpr
    ⟨true,Finset.mem_univ _,false,Finset.mem_univ _,hne⟩
  simpa [w,z,Fintype.prod_bool,Fintype.sum_bool] using h

theorem normalized_holder_strict {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 < f x) (hg0 : ∀ x, 0 < g x)
    (hfint : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = 1)
    (hgint : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = 1)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1) (hne : ¬ f =ᵐ[μ] g) :
    (∫⁻ x, ENNReal.ofReal (f x^b*g x^(1-b)) ∂μ) < 1 := by
  let F : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (f x^b*g x^(1-b))
  let G : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal (b*f x+(1-b)*g x)
  have hb' : 0 < 1-b := sub_pos.mpr hb1
  have hle : ∀ x, F x ≤ G x := by
    intro x
    exact ENNReal.ofReal_le_ofReal (Real.geom_mean_le_arith_mean2_weighted hb.le hb'.le
      (hf0 x).le (hg0 x).le (by ring))
  have hG : Measurable G := ((measurable_const.mul hf).add (measurable_const.mul hg)).ennreal_ofReal
  have hGi : (∫⁻ x, G x ∂μ) = 1 := by
    simp only [G,ENNReal.ofReal_add (mul_nonneg hb.le (hf0 _).le) (mul_nonneg hb'.le (hg0 _).le),
      ENNReal.ofReal_mul hb.le,ENNReal.ofReal_mul hb'.le]
    rw [lintegral_add_left (measurable_const.mul hf.ennreal_ofReal),
      lintegral_const_mul _ hf.ennreal_ofReal,lintegral_const_mul _ hg.ennreal_ofReal,hfint,hgint]
    rw [mul_one,mul_one,← ENNReal.ofReal_add hb.le hb'.le]
    simp
  have hFi : (∫⁻ x, F x ∂μ) ≠ ∞ := ne_top_of_le_ne_top (by rw [hGi]; exact ENNReal.one_ne_top)
    (lintegral_mono hle)
  by_contra h
  have hge : (∫⁻ x, G x ∂μ) ≤ ∫⁻ x, F x ∂μ := by rw [hGi]; exact le_of_not_gt h
  have he := ae_eq_of_ae_le_of_lintegral_le (ae_of_all _ hle) hFi hG.aemeasurable hge
  apply hne
  filter_upwards [he] with x hx
  by_contra hneq
  have hstrict := weighted_geometric_strict b (f x) (g x) hb hb1 (hf0 x).le (hg0 x).le hneq
  have hp : 0 ≤ f x^b*g x^(1-b) := mul_nonneg (Real.rpow_pos_of_pos (hf0 x) _).le
    (Real.rpow_pos_of_pos (hg0 x) _).le
  exact (ne_of_lt (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp |>.mpr hstrict)) hx

/-- Strict Holder with explicit finite, positive marginal moments. -/
theorem holder_strict {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 < f x) (hg0 : ∀ x, 0 < g x) (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hfint : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = ENNReal.ofReal A)
    (hgint : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ENNReal.ofReal B)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1)
    (hne : ¬ (fun x => f x/A) =ᵐ[μ] (fun x => g x/B)) :
    (∫⁻ x, ENNReal.ofReal (f x^b*g x^(1-b)) ∂μ) < ENNReal.ofReal (A^b*B^(1-b)) := by
  have hFn : (∫⁻ x, ENNReal.ofReal (f x/A) ∂μ) = 1 := by
    simp_rw [div_eq_mul_inv,ENNReal.ofReal_mul (hf0 _).le]
    rw [lintegral_mul_const _ hf.ennreal_ofReal,hfint,← ENNReal.ofReal_mul hA.le]
    simp [hA.ne']
  have hGn : (∫⁻ x, ENNReal.ofReal (g x/B) ∂μ) = 1 := by
    simp_rw [div_eq_mul_inv,ENNReal.ofReal_mul (hg0 _).le]
    rw [lintegral_mul_const _ hg.ennreal_ofReal,hgint,← ENNReal.ofReal_mul hB.le]
    simp [hB.ne']
  have hn := normalized_holder_strict μ (fun x => f x/A) (fun x => g x/B)
    (hf.div_const A) (hg.div_const B) (fun x => div_pos (hf0 x) hA) (fun x => div_pos (hg0 x) hB)
    hFn hGn b hb hb1 hne
  let C := A^b*B^(1-b)
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
  have he (x : Ω) : f x^b*g x^(1-b) = C*((f x/A)^b*(g x/B)^(1-b)) := by
    dsimp [C]
    rw [Real.div_rpow (hf0 x).le hA.le,Real.div_rpow (hg0 x).le hB.le]
    field_simp [(Real.rpow_pos_of_pos hA b).ne',(Real.rpow_pos_of_pos hB (1-b)).ne']
  simp_rw [he,ENNReal.ofReal_mul hC.le]
  rw [lintegral_const_mul _ (((hf.div_const A).pow_const b).mul
    ((hg.div_const B).pow_const (1-b))).ennreal_ofReal]
  simpa only [mul_one] using
    (ENNReal.mul_lt_mul_left (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top).mpr hn

end RepeatedEvidenceProbability
