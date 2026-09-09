import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-!
# Formal checks for The price of repeated evidence

These declarations formalize specified components, not the complete probabilistic
monitoring functional. The coverage report records the remaining bridges.
No project-specific axioms or admitted proofs are used.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open scoped BigOperators
open Finset

namespace RepeatedEvidence

section SourceAlgebra
variable {V I : Type*} [Fintype V] [Fintype I]

def load (A : V → I → ℝ) (a : I → ℝ) (v : V) : ℝ := ∑ i, A v i * a i

omit [Fintype V] in
/-- Proposition 1: scaling strictly subunit source loads produces a feasible
fractional matching strictly above the original powers. -/
theorem scaled_fractional_matching (A : V → I → ℝ) (a : I → ℝ) (L : ℝ)
    (hL0 : 0 < L) (hL1 : L < 1) (ha : ∀ i, 0 < a i)
    (hload : ∀ v, load A a v ≤ L) :
    (∀ i, a i < a i / L) ∧ (∀ v, load A (fun i => a i / L) v ≤ 1) := by
  constructor
  · intro i
    apply (lt_div_iff₀ hL0).2
    nlinarith [ha i]
  · intro v
    have hs : load A (fun i => a i / L) v = load A a v / L := by
      simp only [load, div_eq_mul_inv, mul_assoc, sum_mul]
    rw [hs]
    exact (div_le_one hL0).2 (hload v)

/-- Theorem 2: the balancing equations preserve total study power. -/
theorem balance_total (A : V → I → ℝ) (a : I → ℝ) (q : V → ℝ)
    (hbalance : ∀ i, ∑ v, A v i * q v = 1) :
    ∑ i, a i = ∑ v, q v * load A a v := by
  calc
    ∑ i, a i = ∑ i, a i * (∑ v, A v i * q v) := by simp [hbalance]
    _ = ∑ i, ∑ v, q v * (A v i * a i) := by
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro v _
      ring
    _ = ∑ v, q v * load A a v := by rw [sum_comm]; simp [load, mul_sum]

/-- The final exponent identity in the gamma-attainment proof. -/
theorem balanced_exponent (A : V → I → ℝ) (a : I → ℝ) (q : V → ℝ)
    (L : ℝ) (hL : L ≠ 0) (hq : ∀ v, 0 ≤ q v)
    (hbalance : ∀ i, ∑ v, A v i * q v = 1)
    (hactive : ∀ v, 0 < q v → load A a v = L) :
    (∑ i, a i) / L = ∑ v, q v := by
  apply (div_eq_iff hL).2
  rw [balance_total A a q hbalance, sum_mul]
  apply sum_congr rfl
  intro v _
  by_cases h : q v = 0
  · simp [h]
  · rw [hactive v (lt_of_le_of_ne (hq v) (Ne.symm h))]

/-- The positive rational expression displayed as the second derivative.
This proves positivity of the expression, separately from differentiating h. -/
theorem finner_curvature_positive (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 < a ^ 2 / (b * (b - a) ^ 2) := by
  have hb : 0 < b := lt_trans ha hab
  have hba : 0 < b-a := sub_pos.mpr hab
  positivity

/-- Independent leaves and their pooled study cannot have the stated balancing
certificate when there are at least two leaves. -/
theorem pooled_has_no_balancing_certificate (k : ℕ) (hk : 2 ≤ k) :
    ¬ ∃ q : Fin k → ℝ, (∀ j, q j = 1) ∧ (∑ j, q j) = 1 := by
  rintro ⟨q,hq,hs⟩
  simp [hq] at hs
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- Source-load form of the pooled finiteness condition. -/
theorem pooled_load_boundary (a₀ c : ℝ) : a₀ + c < 1 ↔ c < 1 - a₀ := by
  constructor <;> intro h <;> linarith
end SourceAlgebra

/- The weighted count of extensions of r fixed included studies by n free
binary choices, with prescribed parity of the free choices. The recurrence
splits on exclusion or inclusion of the next free study. -/
def parityWeight : ℕ → ℕ → Bool → ℕ
  | 0, r, b => if b then 0 else r
  | n+1, r, b => parityWeight n r b + parityWeight n (r+1) (!b)

/-- General weighted parity identity, for every number of free coordinates. -/
theorem parityWeight_closed (n r : ℕ) (b : Bool) :
    parityWeight (n+2) r b = (2*r+n+2) * 2^n := by
  induction n generalizing r b with
  | zero => cases b <;> simp [parityWeight] <;> omega
  | succ n ih =>
    change parityWeight (n+2) r b + parityWeight (n+2) (r+1) (!b) = _
    rw [ih, ih, pow_succ]
    ring

/-- The overlap-count formula appearing in Theorem 3. -/
theorem overlap_count_formula (m r : ℕ) (h : r+2 ≤ m) (b : Bool) :
    parityWeight (m-r) r b = (m+r) * 2^(m-r-2) := by
  have he : m-r = (m-r-2)+2 := by omega
  rw [he, parityWeight_closed]
  have hc : 2*r+(m-r-2)+2 = m+r := by omega
  rw [hc]
  congr 1

/-- The two parities have equal overlap counts through order m minus two. -/
theorem overlap_parities_equal (m r : ℕ) (h : r+2 ≤ m) :
    parityWeight (m-r) r false = parityWeight (m-r) r true := by
  rw [overlap_count_formula m r h false, overlap_count_formula m r h true]

/-- Total unique-source count of each constructed parity system. -/
theorem parity_union_size (m : ℕ) (hm : 2 ≤ m) (b : Bool) :
    parityWeight m 0 b = m * 2^(m-2) := by
  simpa using overlap_count_formula m 0 hm b

/- Explicit incidence matrices for the four-study construction. Every vector
entry represents a distinct source, including entries with the same bit mask. -/
def maskA : Fin 16 → ℕ := ![3,3,5,5,6,6,9,9,10,10,12,12,15,15,15,15]
def maskB : Fin 16 → ℕ := ![1,2,4,8,7,7,7,11,11,11,13,13,13,14,14,14]
abbrev uses (mask : Fin 16 → ℕ) (v : Fin 16) (i : Fin 4) : Prop :=
  (mask v).testBit i.val = true

def overlap (mask : Fin 16 → ℕ) (R : Finset (Fin 4)) : ℕ :=
  (univ.filter fun v => ∀ i ∈ R, uses mask v i).card

def readCount (mask : Fin 16 → ℕ) (v : Fin 16) : ℕ :=
  (univ.filter fun i => uses mask v i).card

/-- Kernel reduction checks all subsets of at most two studies. -/
theorem four_study_matched_counts :
    ∀ R : Finset (Fin 4), R.card ≤ 2 →
      overlap maskA R = overlap maskB R ∧
      overlap maskA R = if R.card = 0 then 16 else if R.card = 1 then 10 else 6 := by
  decide

theorem four_study_full_counts :
    overlap maskA univ = 4 ∧ overlap maskB univ = 0 := by decide

theorem four_study_maximum_reads :
    (∀ v, readCount maskA v ≤ 4) ∧ (∃ v, readCount maskA v = 4) ∧
    (∀ v, readCount maskB v ≤ 3) ∧ (∃ v, readCount maskB v = 3) := by decide

def certificateB (v : Fin 16) : ℚ := if readCount maskB v = 3 then 1/9 else 0

theorem four_study_B_certificate :
    (∀ v, 0 ≤ certificateB v) ∧
    (∀ i : Fin 4, (∑ v, if uses maskB v i then certificateB v else 0) = 1) ∧
    (∀ v, 0 < certificateB v → readCount maskB v = 3) := by
  constructor
  · intro v
    unfold certificateB
    split <;> norm_num
  constructor
  · intro i
    have hc : (univ.filter fun v : Fin 16 => uses maskB v i ∧ readCount maskB v = 3).card = 9 := by
      revert i
      decide
    have ht : ∀ v, (if uses maskB v i then certificateB v else 0) =
        (if uses maskB v i ∧ readCount maskB v = 3 then (1:ℚ) else 0) / 9 := by
      intro v
      by_cases hi : uses maskB v i
      · rw [if_pos hi]
        by_cases hv : readCount maskB v = 3
        · rw [if_pos ⟨hi,hv⟩]
          simp [certificateB, hv]
        · rw [if_neg (by intro h; exact hv h.2)]
          simp [certificateB, hv]
      · rw [if_neg hi, if_neg (by intro h; exact hi h.1)]
        norm_num

    simp_rw [ht, div_eq_mul_inv]
    rw [← sum_mul]
    simp only [← sum_filter]
    simp [hc]
  · intro v hv
    by_cases h : readCount maskB v = 3
    · exact h
    · simp [certificateB, h] at hv

/-- The displayed power 0.3 lies on opposite sides of the load boundary. -/
theorem four_study_load_separation :
    1 ≤ (4:ℚ)*(3/10) ∧ (3:ℚ)*(3/10) < 1 := by norm_num

/- Exact capped-cost algebra. These definitions are closed expressions;
identification with universal stochastic costs is not asserted here. -/
noncomputable def capMoment (H r : ℝ) : ℝ :=
  if r = 1 then 1 + Real.log H else 1 + r * (H ^ (r-1) - 1) / (r-1)

noncomputable def capCostA (H : ℝ) : ℝ := 6 * H ^ (1/5 : ℝ) - 5
noncomputable def capBoundB (H : ℝ) : ℝ := (10 - 9 * H ^ (-(1/10) : ℝ)) ^ (4/3 : ℝ)

/-- Algebraic specialization of the exact A formula. -/
theorem capMoment_A_formula (H : ℝ) : capMoment H (6/5) = capCostA H := by
  unfold capMoment capCostA
  norm_num
  ring

/-- Algebraic specialization of the moment entering the B upper bound. -/
theorem capMoment_B_formula (H : ℝ) :
    capMoment H (9/10) = 10 - 9 * H ^ (-(1/10) : ℝ) := by
  unfold capMoment
  norm_num
  ring

/-- Order argument in Corollary 3.1, with every cost-bound premise explicit. -/
theorem cap_normalization_penalty (C A B Bupper : ℝ)
    (hA : 0 ≤ A) (hB : 0 < B) (hBU : B ≤ Bupper) (hC : A ≤ C) :
    A / Bupper ≤ C / B := by
  calc
    A / Bupper ≤ A / B := div_le_div_of_nonneg_left hA hB hBU
    _ ≤ C / B := div_le_div_of_nonneg_right hC hB.le

/-- For a fixed realization, selection of reporting times preserves a
nonnegative powered-product upper envelope. -/
theorem reported_product_bound {I : Type*} [Fintype I]
    (M U a : I → ℝ) (K : ℝ) (hM : ∀ i, 0 ≤ M i)
    (hMU : ∀ i, M i ≤ U i) (ha : ∀ i, 0 ≤ a i) (hK : 0 < K) :
    (∏ i, M i ^ a i) / K ≤ (∏ i, U i ^ a i) / K := by
  apply div_le_div_of_nonneg_right _ hK.le
  apply prod_le_prod
  · intro i _; exact Real.rpow_nonneg (hM i) _
  · intro i _; exact Real.rpow_le_rpow (hM i) (hMU i) (ha i)

end RepeatedEvidence
