import Fusion.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Fusion
open Finset

/-- Discrete summation by parts, including both boundary terms. -/
theorem summation_by_parts (a P : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range (n+1), a j * (P (j+1)-P j)) =
    a n * P (n+1) - a 0 * P 0 +
      ∑ j ∈ range n, (a j-a (j+1))*P (j+1) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- The fixed total removes the terminal boundary contribution. -/
theorem summation_by_parts_fixed_total (a P : ℕ → ℝ) (n : ℕ)
    (h0 : P 0 = 0) (hn : P (n+1) = 0) :
    (∑ j ∈ range (n+1), a j*(P (j+1)-P j)) =
    ∑ j ∈ range n, (a j-a (j+1))*P (j+1) := by
  rw [summation_by_parts, h0, hn]; ring

/-- Width of a shared interval bounds the difference of two compatible counts. -/
theorem difference_of_interval (p q l u : ℝ)
    (hp : l ≤ p ∧ p ≤ u) (hq : l ≤ q ∧ q ≤ u) :
    |p-q| ≤ u-l := by
  rw [abs_le]; constructor <;> linarith

/-- Prefix contribution to Equation 6, for any number of bins. -/
theorem prefix_variation_bound (a P w : ℕ → ℝ) (n : ℕ)
    (h0 : P 0 = 0) (hn : P (n+1) = 0)
    (hw : ∀ j < n, |P (j+1)| ≤ w j) :
    |∑ j ∈ range (n+1), a j*(P (j+1)-P j)| ≤
    ∑ j ∈ range n, w j*|a j-a (j+1)| := by
  rw [summation_by_parts_fixed_total a P n h0 hn]
  calc
    _ ≤ ∑ j ∈ range n, |(a j-a (j+1))*P (j+1)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro j hj
      rw [abs_mul, mul_comm (w j)]
      exact mul_le_mul_of_nonneg_left (hw j (mem_range.mp hj)) (abs_nonneg _)

/-- Unreviewed binary-coordinate differences bound the residual term. -/
theorem residual_bound {n : ℕ} (e d : Fin n → ℝ) (O : Finset (Fin n))
    (hreview : ∀ i ∈ O, d i = 0) (hbin : ∀ i, |d i| ≤ 1) :
    |∑ i, e i*d i| ≤ ∑ i ∈ univ \ O, |e i| := by
  have hsum : (∑ i, e i*d i) = ∑ i ∈ univ \ O, e i*d i := by
    symm
    apply sum_subset (Finset.sdiff_subset)
    intro i hi hnot
    have hio : i ∈ O := by simpa using hnot
    simp [hreview i hio]
  rw [hsum]
  calc
    _ ≤ ∑ i ∈ univ \ O, |e i*d i| := abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_left (hbin i) (abs_nonneg (e i))

/-- Assembly of the residual and two prefix contributions. -/
theorem coarsening_assembly (t r p q E VA VB : ℝ)
    (ht : t = r+p+q) (hr : |r| ≤ E) (hp : |p| ≤ VA) (hq : |q| ≤ VB) :
    |t| ≤ E+VA+VB := by
  rw [ht]
  calc
    _ ≤ |r+p|+|q| := abs_add _ _
    _ ≤ (|r|+|p|)+|q| := add_le_add_right (abs_add _ _) _
    _ ≤ _ := by linarith

/-- Monotone coefficients telescope, so the bin count does not multiply the bound. -/
theorem monotone_variation (a : ℕ → ℝ) (n : ℕ) (ha : Monotone a) :
    (∑ j ∈ range n, |a j-a (j+1)|) = a n-a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, abs_of_nonpos (sub_nonpos.mpr (ha (Nat.le_succ n)))]
    ring

theorem two_rank_variations (N VA VB : ℝ)
    (ha : VA ≤ 4*(N-1)) (hb : VB ≤ 4*(N-1)) :
    VA+VB ≤ 8*(N-1) := by linarith


def prefixCount {N : ℕ} (g : Fin N → ℕ) (y : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => g i < j), y i

def realGroupCount {N : ℕ} (g : Fin N → ℕ) (y : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ univ.filter (fun i => g i = j), y i

theorem prefix_difference {N : ℕ} (g : Fin N → ℕ) (y z : Fin N → ℝ) (j : ℕ) :
    prefixCount g (fun i => y i-z i) j = prefixCount g y j-prefixCount g z j := by
  simp [prefixCount,sum_sub_distrib]

theorem bin_is_prefix_increment {N : ℕ} (g : Fin N → ℕ) (y : Fin N → ℝ) (j : ℕ) :
    realGroupCount g y j = prefixCount g y (j+1)-prefixCount g y j := by
  simp only [realGroupCount,prefixCount,sum_filter,← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  by_cases h : g i < j
  · have hnext : g i < j+1 := by omega
    have hne : g i ≠ j := by omega
    simp [h,hnext,hne]
  · by_cases he : g i = j
    · simp [he]
    · have hnext : ¬g i < j+1 := by omega
      simp [h,hnext,he]

theorem grouped_weight_sum {N n : ℕ} (g : Fin N → ℕ) (a : ℕ → ℝ)
    (y : Fin N → ℝ) (hg : ∀ i, g i < n+1) :
    (∑ i, a (g i)*y i) =
    ∑ j ∈ range (n+1), a j*(prefixCount g y (j+1)-prefixCount g y j) := by
  have hsum := sum_fiberwise_of_maps_to (s := univ) (t := range (n+1))
    (g := g) (fun i _ => mem_range.mpr (hg i)) (fun i => a (g i)*y i)
  rw [← hsum]
  apply sum_congr rfl
  intro j hj
  rw [← bin_is_prefix_increment,realGroupCount,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [(mem_filter.mp hi).2]

theorem prefix_at_zero {N : ℕ} (g : Fin N → ℕ) (y : Fin N → ℝ) :
    prefixCount g y 0 = 0 := by simp [prefixCount]

theorem prefix_at_total {N n : ℕ} (g : Fin N → ℕ) (y : Fin N → ℝ)
    (hg : ∀ i, g i < n+1) : prefixCount g y (n+1) = ∑ i, y i := by
  simp [prefixCount,hg]

/-- Full numerator form of Equation 6, with group memberships, common count
    intervals, fixed total, and reviewed records represented explicitly.
    This holds even for continuous completions in [0,1], hence for binary ones. -/
theorem coarsening_bound {N n m : ℕ} (gA gB : Fin N → ℕ)
    (a e y z : Fin N → ℝ) (alpha beta lA uA lB uB : ℕ → ℝ)
    (O : Finset (Fin N))
    (hgA : ∀ i, gA i < n+1) (hgB : ∀ i, gB i < m+1)
    (hcoef : ∀ i, a i = alpha (gA i)+beta (gB i)+e i)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hrev : ∀ i ∈ O, y i = z i) (htotal : (∑ i, y i) = ∑ i, z i)
    (hAy : ∀ j < n, lA j ≤ prefixCount gA y (j+1) ∧ prefixCount gA y (j+1) ≤ uA j)
    (hAz : ∀ j < n, lA j ≤ prefixCount gA z (j+1) ∧ prefixCount gA z (j+1) ≤ uA j)
    (hBy : ∀ j < m, lB j ≤ prefixCount gB y (j+1) ∧ prefixCount gB y (j+1) ≤ uB j)
    (hBz : ∀ j < m, lB j ≤ prefixCount gB z (j+1) ∧ prefixCount gB z (j+1) ≤ uB j) :
    |∑ i, a i*(y i-z i)| ≤
      (∑ i ∈ univ \ O, |e i|) +
      (∑ j ∈ range n, (uA j-lA j)*|alpha j-alpha (j+1)|) +
      (∑ j ∈ range m, (uB j-lB j)*|beta j-beta (j+1)|) := by
  let d : Fin N → ℝ := fun i => y i-z i
  have hd : ∀ i, |d i| ≤ 1 := by
    intro i
    simpa [d] using difference_of_interval (y i) (z i) 0 1 (hy i) (hz i)
  have hdr : ∀ i ∈ O, d i=0 := by intro i hi; simp [d,hrev i hi]
  have hdt : (∑ i, d i)=0 := by simp [d,sum_sub_distrib,htotal]
  have hPA0 : prefixCount gA d 0=0 := prefix_at_zero _ _
  have hPB0 : prefixCount gB d 0=0 := prefix_at_zero _ _
  have hPAt : prefixCount gA d (n+1)=0 := (prefix_at_total _ _ hgA).trans hdt
  have hPBt : prefixCount gB d (m+1)=0 := (prefix_at_total _ _ hgB).trans hdt
  have hPA : ∀ j < n, |prefixCount gA d (j+1)| ≤ uA j-lA j := by
    intro j hj
    rw [show d = (fun i => y i-z i) from rfl,prefix_difference]
    exact difference_of_interval _ _ _ _ (hAy j hj) (hAz j hj)
  have hPB : ∀ j < m, |prefixCount gB d (j+1)| ≤ uB j-lB j := by
    intro j hj
    rw [show d = (fun i => y i-z i) from rfl,prefix_difference]
    exact difference_of_interval _ _ _ _ (hBy j hj) (hBz j hj)
  have hA := prefix_variation_bound alpha (prefixCount gA d) (fun j => uA j-lA j) n hPA0 hPAt hPA
  have hB := prefix_variation_bound beta (prefixCount gB d) (fun j => uB j-lB j) m hPB0 hPBt hPB
  rw [← grouped_weight_sum gA alpha d hgA] at hA
  rw [← grouped_weight_sum gB beta d hgB] at hB
  apply coarsening_assembly _ (∑ i,e i*d i) (∑ i,alpha (gA i)*d i)
    (∑ i,beta (gB i)*d i) _ _ _ _ (residual_bound e d O hdr hd) hA hB
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  rw [hcoef i]
  dsimp [d]
  ring

end Fusion
