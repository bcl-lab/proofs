import HubAveraging

set_option maxHeartbeats 5000000
namespace HubAveraging
noncomputable section
open Finset
variable {V : Type*} [DecidableEq V]

/- Select each next leaf uniformly among those remaining. The horizon is the
initial number of leaves. This is the sequential uniform-permutation sampler. -/
def randomSweepLoss (x : V → ℝ) : ℕ → Finset V → ℝ → ℝ
  | 0, _, _ => 0
  | n+1, s, h => (∑ i ∈ s, ((h-x i)^2/2 +
      randomSweepLoss x n (s.erase i) ((h+x i)/2))) / s.card

def localFormula (d : ℕ) (h t q : ℝ) : ℝ :=
  a d*(q-t^2/d) + (2/3 : ℝ)*(1-r d)*(h-t/d)^2

/- Polynomial coefficients in one recursion of uniform sampling. -/
def recA (n : ℕ) : ℝ := 1/2 + (2/3 : ℝ)*(1-r n)/4
def recB (n : ℕ) : ℝ := -1/(n+1) + (2/3 : ℝ)*(1-r n)/(2*(n+1)) -
  ((2/3 : ℝ)*(1-r n)/n)*n/(n+1)
def recC (n : ℕ) : ℝ := -((2/3 : ℝ)*(1-r n)/n)/(n+1) +
  (((2/3 : ℝ)*(1-r n)/n-a n)/n)*((n : ℝ)-1)/(n+1)
def recD (n : ℕ) : ℝ := 1/(2*(n+1)) + (2/3 : ℝ)*(1-r n)/(4*(n+1)) +
  ((2/3 : ℝ)*(1-r n)/n)/(n+1) +
  (((2/3 : ℝ)*(1-r n)/n-a n)/n)/(n+1) + a n*n/(n+1)

theorem localFormula_recurrence_coefficients (n : ℕ) (hn : 1 ≤ n) :
    recA n = (2/3 : ℝ)*(1-r (n+1)) ∧
    recB n = -2*((2/3 : ℝ)*(1-r (n+1)))/(n+1) ∧
    recC n = (((2/3 : ℝ)*(1-r (n+1)))/(n+1)-a (n+1))/(n+1) ∧
    recD n = a (n+1) := by
  by_cases h1 : n = 1
  · subst n
    norm_num [recA, recB, recC, recD, a, alpha, r]
  · have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hnm : (n : ℝ)-1 ≠ 0 := by linarith
    have hnp : (n : ℝ)+1 ≠ 0 := by positivity
    unfold recA recB recC recD a alpha r
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    constructor
    · ring
    constructor
    · field_simp; ring
    constructor <;> field_simp <;> ring

/- One-step expectation algebra, after summing over all possible first leaves. -/
omit [DecidableEq V] in
theorem localFormula_average (n : ℕ) (hn : 1 ≤ n) (s : Finset V)
    (hc : s.card = n+1) (x : V → ℝ) (h : ℝ) :
    (∑ i ∈ s, ((h-x i)^2/2 +
      localFormula n ((h+x i)/2) ((∑ j ∈ s, x j)-x i)
        ((∑ j ∈ s, (x j)^2)-(x i)^2))) / s.card =
    localFormula (n+1) h (∑ j ∈ s, x j) (∑ j ∈ s, (x j)^2) := by
  let t := ∑ j ∈ s, x j
  let q := ∑ j ∈ s, (x j)^2
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hnp : (n : ℝ)+1 ≠ 0 := by positivity
  have hp (z : ℝ) : (h-z)^2/2 + localFormula n ((h+z)/2) (t-z) (q-z^2) =
      (1/2+(2/3 : ℝ)*(1-r n)/4)*h^2 - ((2/3 : ℝ)*(1-r n)/n)*h*t +
      (((2/3 : ℝ)*(1-r n)/n-a n)/n)*t^2 + a n*q +
      (-h+(2/3 : ℝ)*(1-r n)*h/2+((2/3 : ℝ)*(1-r n)/n)*h -
        ((2/3 : ℝ)*(1-r n)/n)*t - 2*(((2/3 : ℝ)*(1-r n)/n-a n)/n)*t)*z +
      (1/2+(2/3 : ℝ)*(1-r n)/4+((2/3 : ℝ)*(1-r n)/n)+
        (((2/3 : ℝ)*(1-r n)/n-a n)/n)-a n)*z^2 := by
    unfold localFormula
    field_simp
    ring
  change (∑ i ∈ s, ((h-x i)^2/2 + localFormula n ((h+x i)/2) (t-x i) (q-(x i)^2))) / (s.card : ℝ) = _
  simp_rw [hp]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← mul_sum, hc, Nat.cast_add, Nat.cast_one]
  change _ = localFormula (n+1) h t q
  have he : localFormula (n+1) h t q = recA n*h^2 + recB n*h*t + recC n*t^2 + recD n*q := by
    obtain ⟨hA,hB,hC,hD⟩ := localFormula_recurrence_coefficients n hn
    rw [hA,hB,hC,hD]
    unfold localFormula
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  rw [he]
  unfold recA recB recC recD
  field_simp
  ring

/- The full exact local expectation, derived by sampling without replacement. -/
theorem randomSweepLoss_formula (x : V → ℝ) (n : ℕ) (s : Finset V)
    (hc : s.card = n) (h : ℝ) :
    randomSweepLoss x n s h = localFormula n h (∑ i ∈ s, x i) (∑ i ∈ s, (x i)^2) := by
  induction n generalizing s h with
  | zero =>
    have hs : s = ∅ := card_eq_zero.mp hc
    subst s
    simp [randomSweepLoss, localFormula, r]
  | succ n ih =>
    cases n with
    | zero =>
      obtain ⟨i,hi⟩ := card_eq_one.mp hc
      subst s
      norm_num [randomSweepLoss, localFormula, a, alpha, r]
      ring
    | succ n =>
      rw [randomSweepLoss]
      have he (i : V) (hi : i ∈ s) :
          randomSweepLoss x (n+1) (s.erase i) ((h+x i)/2) =
          localFormula (n+1) ((h+x i)/2) ((∑ j ∈ s, x j)-x i)
            ((∑ j ∈ s, (x j)^2)-(x i)^2) := by
        rw [ih (s.erase i) (by rw [card_erase_of_mem hi, hc]; omega)]
        have ht := sum_erase_add s x hi
        have hq := sum_erase_add s (fun j => (x j)^2) hi
        dsimp at hq
        rw [show (∑ j ∈ s.erase i, x j) = (∑ j ∈ s, x j)-x i by linarith,
          show (∑ j ∈ s.erase i, (x j)^2) = (∑ j ∈ s, (x j)^2)-(x i)^2 by linarith]
      calc
        _ = (∑ i ∈ s, ((h-x i)^2/2 +
            localFormula (n+1) ((h+x i)/2) ((∑ j ∈ s, x j)-x i)
              ((∑ j ∈ s, (x j)^2)-(x i)^2))) / (s.card : ℝ) := by
          congr 1
          apply sum_congr rfl
          intro i hi
          rw [he i hi]
        _ = _ := localFormula_average (n+1) (by omega) s hc x h

end
end HubAveraging
