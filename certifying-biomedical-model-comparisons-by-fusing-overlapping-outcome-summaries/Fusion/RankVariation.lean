import Fusion.Variation
import Fusion.Disjoint

namespace Fusion
open Finset

/-- A bounded nonnegative width scales total variation without a bin-count factor. -/
theorem weighted_monotone_variation (a w : ℕ → ℝ) (n : ℕ) (W : ℝ)
    (ha : Monotone a) (hw : ∀ j < n,w j ≤ W) :
    (∑ j ∈ range n,w j*|a j-a (j+1)|) ≤ W*(a n-a 0) := by
  calc
    _ ≤ ∑ j ∈ range n,W*|a j-a (j+1)| := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hw j (mem_range.mp hj)) (abs_nonneg _)
    _ = _ := by rw [← mul_sum,monotone_variation a n ha]

theorem weighted_antitone_variation (a w : ℕ → ℝ) (n : ℕ) (W : ℝ)
    (ha : Antitone a) (hw : ∀ j < n,w j ≤ W) :
    (∑ j ∈ range n,w j*|a j-a (j+1)|) ≤ W*(a 0-a n) := by
  have hn : Monotone (fun j => -a j) := by intro i j hij; exact neg_le_neg (ha hij)
  have h := weighted_monotone_variation (fun j => -a j) w n W hn hw
  have he : ∀ j, |(-a j)-(-a (j+1))| = |a j-a (j+1)| := by
    intro j
    rw [show -a j - -a (j+1) = -(a j-a (j+1)) by ring,abs_neg]
  dsimp only at h
  simp only [he] at h
  convert h using 1 <;> ring

/-- The stated 8(N-1) cumulative rank contribution, allowing any bin counts. -/
theorem rank_prefix_eight_bound (alpha beta wA wB : ℕ → ℝ) (n m : ℕ) (N : ℝ)
    (ha : Monotone alpha) (hb : Antitone beta)
    (ha0 : 1 ≤ alpha 0) (han : alpha n ≤ N)
    (hb0 : beta 0 ≤ -1) (hbm : -N ≤ beta m)
    (hwA : ∀ j < n,wA j ≤ 4) (hwB : ∀ j < m,wB j ≤ 4) :
    (∑ j ∈ range n,wA j*|alpha j-alpha (j+1)|) +
    (∑ j ∈ range m,wB j*|beta j-beta (j+1)|) ≤ 8*(N-1) := by
  have hA := weighted_monotone_variation alpha wA n 4 ha hwA
  have hB := weighted_antitone_variation beta wB m 4 hb hwB
  linarith

/-- Clipping compatible intervals cannot increase their width. -/
theorem clipped_width (l u L U W : ℝ) (h : u-l ≤ W) :
    min u U-max l L ≤ W := by
  have hl := le_max_left l L
  have hu := min_le_left u U
  linarith

end Fusion
