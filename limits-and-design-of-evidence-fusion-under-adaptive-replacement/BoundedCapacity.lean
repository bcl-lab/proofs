import CapacityBoundary

open scoped BigOperators NNReal
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

theorem retained_fraction_monotone (r t p : ℕ) (ht : 0 < t) (htp : t ≤ p) :
    ((t-r : ℕ) : ℝ)/(t : ℝ) ≤ ((p-r : ℕ) : ℝ)/(p : ℝ) := by
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hpr : (0 : ℝ) < p := by exact_mod_cast ht.trans_le htp
  by_cases hrt : r ≤ t
  · rw [Nat.cast_sub hrt,Nat.cast_sub (hrt.trans htp)]
    apply (div_le_div_iff₀ htr hpr).mpr
    have htp' : (t : ℝ) ≤ p := by exact_mod_cast htp
    nlinarith [mul_nonneg (Nat.cast_nonneg r) (sub_nonneg.mpr htp')]
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hrt)]
    simp only [Nat.cast_zero,zero_div]
    exact div_nonneg (Nat.cast_nonneg _) hpr.le

theorem prefix_reciprocal_lower {p : ℕ} (x : Fin p → ℝ) (hx : ∀ i, 0 < x i)
    (B : ℝ) (hB : 0 < B) (hbound : ∀ i, x i ≤ B) (j : Fin p) :
    ((j : ℕ)+1 : ℝ)/B ≤ prefixReciprocal x j := by
  have he : (∑ i : Fin p, if i ≤ j then 1/B else 0) = ((j : ℕ)+1 : ℝ)/B := by
    rw [← Finset.sum_filter]
    have hs : Finset.univ.filter (fun i : Fin p => i ≤ j)=Finset.Iic j := by ext i; simp
    rw [hs]
    simp [div_eq_mul_inv]
  rw [← he]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact one_div_le_one_div_of_le (hx i) (hbound i)
  · exact le_rfl

theorem bounded_positive_capacity {p : ℕ} [NeZero p] (x : Fin p → ℝ)
    (hx : ∀ i, 0 < x i) (B : ℝ) (hB : 0 < B) (hbound : ∀ i, x i ≤ B) (r : ℕ) :
    positiveCapacity x r ≤ B*((p-r : ℕ) : ℝ)/(p : ℝ) := by
  apply Finset.sup'_le Finset.univ_nonempty
  intro j _
  have hpref := prefix_reciprocal_lower x hx B hB hbound j
  have ht : (0 : ℝ) < (j : ℕ)+1 := by positivity
  have hb := div_le_div_of_nonneg_left (Nat.cast_nonneg ((j : ℕ)+1-r))
    (div_pos ht hB) hpref
  have he : (((j : ℕ)+1-r : ℕ) : ℝ)/(((j : ℕ)+1 : ℝ)/B) =
      B*((((j : ℕ)+1-r : ℕ) : ℝ)/((j : ℕ)+1 : ℝ)) := by field_simp; ring
  rw [he] at hb
  have hm := mul_le_mul_of_nonneg_left (retained_fraction_monotone r ((j : ℕ)+1) p
    (Nat.succ_pos _) j.isLt) hB.le
  simp only [Nat.cast_add,Nat.cast_one] at hm
  simpa only [mul_div_assoc] using hb.trans hm

theorem equal_signal_capacity {p : ℕ} [NeZero p] (B : ℝ) (hB : 0 < B) (r : ℕ) :
    positiveCapacity (fun _ : Fin p => B) r = B*((p-r : ℕ) : ℝ)/(p : ℝ) := by
  apply le_antisymm (bounded_positive_capacity _ (fun _ => hB) B hB (fun _ => le_rfl) r)
  let j : Fin p := ⟨p-1,by have hp := NeZero.pos p; omega⟩
  have hj : (j : ℕ)+1=p := by dsimp [j]; have hp := NeZero.pos p; omega
  have he : prefixReciprocal (fun _ : Fin p => B) j=(p : ℝ)/B := by
    unfold prefixReciprocal
    have hall (i : Fin p) : i ≤ j := by change (i : ℕ) ≤ p-1; omega
    simp [hall,div_eq_mul_inv]
  have hh := Finset.le_sup' (fun i : Fin p =>
    (((i : ℕ)+1-r : ℕ) : ℝ)/prefixReciprocal (fun _ : Fin p => B) i) (Finset.mem_univ j)
  change _ ≤ positiveCapacity (fun _ : Fin p => B) r at hh
  rw [hj,he] at hh
  have heq : ((p-r : ℕ) : ℝ)/((p : ℝ)/B)=B*((p-r : ℕ) : ℝ)/(p : ℝ) := by field_simp; ring
  rwa [heq] at hh

theorem positive_capacity_zero_of_budget {p : ℕ} [NeZero p] (x : Fin p → ℝ)
    (hx : ∀ i, 0 < x i) (r : ℕ) (hr : p ≤ r) : positiveCapacity x r=0 := by
  apply le_antisymm _ (positiveCapacity_nonneg x hx r)
  apply Finset.sup'_le Finset.univ_nonempty
  intro j _
  have hj : (j : ℕ)+1-r=0 := by omega
  simp [hj]

/-- S15's ceiling bound derived from the full capacity expression. -/
theorem bounded_report_count {p n : ℕ} [NeZero p] (x : Fin p → ℝ)
    (hx : ∀ i, 0 < x i) (hpn : p ≤ n) (k : ℕ)
    (B T : ℝ) (hT : 1 < T) (hBT : T < B) (hbound : ∀ i, x i ≤ B)
    (hreaches : T ≤ max 1 (positiveCapacity x (min n (2*k)))) :
    Nat.ceil (2*(k : ℝ)*B/(B-T)) ≤ p := by
  have hB : 0 < B := lt_trans (by linarith) hBT
  have hc : T ≤ positiveCapacity x (min n (2*k)) := (le_max_iff.mp hreaches).resolve_left (not_le.mpr hT)
  have hrp : min n (2*k) < p := by
    by_contra hn
    have he := positive_capacity_zero_of_budget x hx _ (Nat.le_of_not_gt hn)
    rw [he] at hc
    linarith
  have hkn : 2*k ≤ n := by omega
  have hkp : 2*k ≤ p := by omega
  rw [Nat.min_eq_right hkn] at hc
  have hb := hc.trans (bounded_positive_capacity x hx B hB hbound (2*k))
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  rw [Nat.cast_sub hkp,Nat.cast_mul,Nat.cast_ofNat] at hb
  have hmul := (le_div_iff₀ hp).mp hb
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (sub_pos.mpr hBT)).mpr
  nlinarith

/-- Sharpness of S15 for equal positive reports, with the general integer ceiling. -/
theorem equal_signal_capacity_threshold_iff {p n : ℕ} [NeZero p] (hpn : p ≤ n) (k : ℕ)
    (B T : ℝ) (hT : 1 < T) (hBT : T < B) :
    T ≤ max 1 (positiveCapacity (fun _ : Fin p => B) (min n (2*k))) ↔
      Nat.ceil (2*(k : ℝ)*B/(B-T)) ≤ p := by
  have hB : 0 < B := lt_trans (by linarith) hBT
  constructor
  · exact bounded_report_count _ (fun _ => hB) hpn k B T hT hBT (fun _ => le_rfl)
  · intro hc
    have hreal := (div_le_iff₀ (sub_pos.mpr hBT)).mp (Nat.ceil_le.mp hc)
    have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
    have hkp : 2*k < p := by
      by_contra hn
      have hnp : p ≤ 2*k := Nat.le_of_not_gt hn
      have hcast : (p : ℝ) ≤ 2*(k : ℝ) := by exact_mod_cast hnp
      nlinarith [mul_le_mul_of_nonneg_right hcast hB.le]
    have hkn : 2*k ≤ n := hkp.le.trans hpn
    apply le_trans _ (le_max_right _ _)
    rw [Nat.min_eq_right hkn,equal_signal_capacity B hB,Nat.cast_sub hkp.le,
      Nat.cast_mul,Nat.cast_ofNat]
    exact (le_div_iff₀ hp).mpr (by nlinarith)

end
end EvidenceFusion
