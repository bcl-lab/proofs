import RepeatedEvidence

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace RepeatedEvidence

/-- An exact algebraic certificate for the ratio of the two capped-cost
expressions. Root enclosures and polynomial comparisons are explicit premises. -/
theorem cap_ratio_from_root_certificate (H xl xu yu r : ℝ)
    (hH : 0 < H) (hxl : 0 < xl) (hxu : 0 ≤ xu)
    (hlo : xl^10 ≤ H) (hhi : H ≤ xu^10)
    (hzlo : 0 < 10 - 9/xl) (hyu : 0 < yu) (hr : 0 ≤ r)
    (hpoly : (10 - 9/xu)^4 ≤ yu^3)
    (hnum : r*yu ≤ 6*xl^2 - 5) :
    r ≤ capCostA H / capBoundB H := by
  let x : ℝ := H ^ (1/10 : ℝ)
  have hx : 0 < x := Real.rpow_pos_of_pos hH _
  have hx10 : x^10 = H := by
    simpa [x, one_div] using Real.rpow_inv_natCast_pow hH.le (by decide : (10:ℕ) ≠ 0)
  have hxlx : xl ≤ x := by
    apply (pow_le_pow_iff_left₀ hxl.le hx.le (by decide : (10:ℕ) ≠ 0)).1
    simpa [hx10] using hlo
  have hxxu : x ≤ xu := by
    apply (pow_le_pow_iff_left₀ hx.le hxu (by decide : (10:ℕ) ≠ 0)).1
    simpa [hx10] using hhi
  let z : ℝ := 10 - 9/x
  have hz : 0 < z := by
    have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 9) hxl hxlx
    dsimp [z]
    linarith
  have hzupper : z ≤ 10 - 9/xu := by
    have hd := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 9) hx hxxu
    dsimp [z]
    linarith
  have hB : capBoundB H = z ^ (4/3 : ℝ) := by
    unfold capBoundB
    congr 1
    rw [Real.rpow_neg hH.le]
    simp [z, x, div_eq_mul_inv]
  have hBpos : 0 < capBoundB H := by rw [hB]; exact Real.rpow_pos_of_pos hz _
  have hBcube : (capBoundB H)^3 = z^4 := by
    rw [hB, ← Real.rpow_mul_natCast hz.le]
    norm_num
    exact Real.rpow_natCast z 4
  have hByu : capBoundB H ≤ yu := by
    apply (pow_le_pow_iff_left₀ hBpos.le hyu.le (by decide : (3:ℕ) ≠ 0)).1
    rw [hBcube]
    exact (pow_le_pow_left₀ hz.le hzupper 4).trans hpoly
  have hA : capCostA H = 6*x^2 - 5 := by
    unfold capCostA
    have he : H ^ (1/5 : ℝ) = x^2 := by
      dsimp [x]
      rw [← Real.rpow_mul_natCast hH.le]
      norm_num
    rw [he]
  apply (le_div_iff₀ hBpos).2
  rw [hA]
  calc
    r * capBoundB H ≤ r * yu := mul_le_mul_of_nonneg_left hByu hr
    _ ≤ 6*xl^2 - 5 := hnum
    _ ≤ 6*x^2 - 5 := by nlinarith [pow_le_pow_left₀ hxl.le hxlx 2]

/-- The manuscript's 5.88 lower bound, certified by exact rational arithmetic
and monotonicity of real powers. No floating-point premise is used. -/
theorem cap_ratio_million : (588/100 : ℝ) ≤ capCostA 1000000 / capBoundB 1000000 := by
  apply cap_ratio_from_root_certificate 1000000 (3981/1000) (3982/1000) (1531/100) (588/100)
  all_goals norm_num

/-- The manuscript's 75.37 lower bound, with exact root enclosures. -/
theorem cap_ratio_trillion : (7537/100 : ℝ) ≤
    capCostA 1000000000000 / capBoundB 1000000000000 := by
  apply cap_ratio_from_root_certificate 1000000000000
    (1584893/100000) (1584894/100000) (199288/10000) (7537/100)
  all_goals norm_num

end RepeatedEvidence
