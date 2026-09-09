import DelayedGrowth

open scoped BigOperators Topology
open Finset Set Filter
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

def dyadicFraction (j : ℕ) : ℝ :=
  ((2*((j+1)-2^(j+1).log2)+1 : ℕ) : ℝ) / ((2^((j+1).log2+1) : ℕ) : ℝ)

def activeCount (n : ℕ) : ℕ := if n=0 then 0 else n.log2+1

theorem activeCount_zero : activeCount 0=0 := by simp [activeCount]

theorem activeCount_characterization (n j : ℕ) : j < activeCount n ↔ 2^j ≤ n := by
  by_cases hn : n=0
  · subst n
    simp [activeCount,Nat.two_pow_pos]
  · simp only [activeCount,hn,if_false,Nat.lt_succ_iff]
    exact Nat.le_log2 hn

theorem activeCount_monotone : Monotone activeCount := by
  intro n t hnt
  by_contra hn
  have hj : activeCount t < activeCount n := Nat.lt_of_not_ge hn
  have hh := (activeCount_characterization n (activeCount t)).mp hj
  have ht := (activeCount_characterization t (activeCount t)).mpr (hh.trans hnt)
  exact (lt_irrefl _) ht

theorem activeCount_eventually (j : ℕ) : ∀ᶠ n : ℕ in atTop, j < activeCount n := by
  filter_upwards [eventually_ge_atTop (2^j)] with n hn
  exact (activeCount_characterization n j).mpr hn

theorem log2_dyadic_block (m q : ℕ) (hq : q < 2^m) : (2^m+q).log2=m := by
  have hp : 0 < 2^m := Nat.two_pow_pos m
  have hn : 2^m+q ≠ 0 := by omega
  apply Nat.eq_of_le_of_lt_succ
  · exact (Nat.le_log2 hn).mpr (Nat.le_add_right _ _)
  · apply (Nat.log2_lt hn).mpr
    rw [pow_succ]
    omega

theorem dyadicFraction_block (m q : ℕ) (hq : q < 2^m) :
    dyadicFraction (2^m+q-1) = (2*(q : ℝ)+1)/(2*(2 : ℝ)^m) := by
  have hp := Nat.two_pow_pos m
  have he : 2^m+q-1+1=2^m+q := by omega
  unfold dyadicFraction
  rw [he,log2_dyadic_block m q hq]
  simp only [Nat.add_sub_cancel_left,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
    Nat.cast_ofNat,Nat.cast_pow,pow_succ]
  ring

theorem dyadicFraction_mem (j : ℕ) : dyadicFraction j ∈ Set.Ioo 0 1 := by
  let m := (j+1).log2
  let q := j+1-2^m
  have hlo : 2^m ≤ j+1 := Nat.log2_self_le (Nat.succ_ne_zero j)
  have hhi : j+1 < 2^m*2 := by simpa [m,pow_succ] using (Nat.lt_log2_self (n := j+1))
  have hq : q < 2^m := by dsimp [q]; omega
  have hj : j=2^m+q-1 := by dsimp [q]; omega
  rw [hj,dyadicFraction_block m q hq]
  have hqr : (q : ℝ)+1 ≤ (2 : ℝ)^m := by exact_mod_cast hq
  have hpow : 0 < (2 : ℝ)^m := by positivity
  constructor
  · positivity
  · apply (div_lt_one (by positivity : 0 < 2*(2 : ℝ)^m)).mpr
    linarith

theorem dyadicFraction_dense (u eps : ℝ) (hu : u ∈ Set.Ioo 0 1) (he : 0 < eps) :
    ∃ j : ℕ, |dyadicFraction j-u| < eps := by
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt (1/eps) (by norm_num : (1 : ℝ) < 2)
  have hp : 0 < (2 : ℝ)^m := by positivity
  let q := Nat.floor (u*(2 : ℝ)^m)
  have hq : q < 2^m := by
    apply (Nat.floor_lt (mul_nonneg hu.1.le hp.le)).mpr
    norm_num only [Nat.cast_pow,Nat.cast_ofNat]
    simpa only [one_mul] using mul_lt_mul_of_pos_right hu.2 hp
  refine ⟨2^m+q-1,?_⟩
  rw [dyadicFraction_block m q hq]
  have hlow := Nat.floor_le (mul_nonneg hu.1.le hp.le)
  have hhigh := Nat.lt_floor_add_one (u*(2 : ℝ)^m)
  change (q : ℝ) ≤ u*(2 : ℝ)^m at hlow
  change u*(2 : ℝ)^m < (q : ℝ)+1 at hhigh
  have hwidth : 1 < eps*(2 : ℝ)^m := by
    simpa only [mul_comm] using (div_lt_iff₀ he).mp hm
  apply abs_lt.mpr
  constructor
  · rw [lt_sub_iff_add_lt,lt_div_iff₀ (by positivity : 0 < 2*(2 : ℝ)^m)]
    nlinarith
  · rw [sub_lt_iff_lt_add,div_lt_iff₀ (by positivity : 0 < 2*(2 : ℝ)^m)]
    nlinarith

end
end EvidenceFusion
