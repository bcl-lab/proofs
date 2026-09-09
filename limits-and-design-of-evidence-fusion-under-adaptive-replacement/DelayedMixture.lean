import TwoLayer

open scoped BigOperators NNReal ENNReal Topology
open Finset Set MeasureTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

def delayedPrior (j : ℕ) : ℝ := 1/((j+1 : ℝ)*(j+2))

theorem delayedPrior_pos (j : ℕ) : 0 < delayedPrior j := by unfold delayedPrior; positivity

def fixedPriorMixture (E : ℕ → ℕ → Ω → ℝ) (K : ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  1+∑ j ∈ Finset.range K, (delayedPrior j/2)*(E j n ω-1)

def delayedMixture (E : ℕ → ℕ → Ω → ℝ) (J : ℕ → ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  1/2 + (1/2)*∑ j ∈ Finset.range (J n), delayedPrior j*E j n ω + 1/(2*(J n+1 : ℝ))

theorem fixedPriorMixture_formula (E : ℕ → ℕ → Ω → ℝ) (K n : ℕ) (ω : Ω) :
    fixedPriorMixture E K n ω =
      1/2 + (1/2)*∑ j ∈ Finset.range K, delayedPrior j*E j n ω + 1/(2*(K+1 : ℝ)) := by
  have hm := delayed_prior_mass K
  change (∑ j ∈ Finset.range K, delayedPrior j) = 1-1/(K+1 : ℝ) at hm
  unfold fixedPriorMixture
  have he : (∑ j ∈ Finset.range K, (delayedPrior j/2)*(E j n ω-1)) =
      (1/2)*(∑ j ∈ Finset.range K, delayedPrior j*E j n ω) -
        (1/2)*(∑ j ∈ Finset.range K, delayedPrior j) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,hm]
  field_simp
  <;> ring

theorem fixedPriorMixture_supermartingale (E : ℕ → ℕ → Ω → ℝ)
    (hE : ∀ j, Supermartingale (E j) ℱ μ) (K : ℕ) :
    Supermartingale (fixedPriorMixture E K) ℱ μ := by
  induction K with
  | zero =>
    have he : fixedPriorMixture E 0 = fun _ _ => (1 : ℝ) := by
      funext n ω; simp [fixedPriorMixture]
    rw [he]
    exact (martingale_const ℱ μ 1).supermartingale
  | succ K ih =>
    have hterm := ((hE K).sub_martingale (martingale_const ℱ μ 1)).smul_nonneg
      (div_nonneg (delayedPrior_pos K).le (by norm_num : (0 : ℝ) ≤ 2))
    have he : fixedPriorMixture E (K+1) = fixedPriorMixture E K +
        (delayedPrior K/2) • (E K - (fun _ _ => (1 : ℝ))) := by
      funext n ω
      simp [fixedPriorMixture,Finset.sum_range_succ,add_assoc]
    rw [he]
    exact ih.add hterm

theorem fixedPriorMixture_extension (E : ℕ → ℕ → Ω → ℝ) (J K n : ℕ) (hJK : J ≤ K)
    (hinactive : ∀ j, J ≤ j → E j n = 1) : fixedPriorMixture E K n = fixedPriorMixture E J n := by
  funext ω
  unfold fixedPriorMixture
  congr 1
  symm
  apply Finset.sum_subset (Finset.range_mono hJK)
  intro j hjK hjJ
  have hj : J ≤ j := Nat.le_of_not_gt (by simpa using hjJ)
  simp [hinactive j hj]

/-- A finite implementation of the infinite mixture is a supermartingale.
All inactive components equal one, so no interchange of unevaluated infinite
sums with conditional expectations is assumed. -/
theorem delayedMixture_supermartingale (E : ℕ → ℕ → Ω → ℝ) (J : ℕ → ℕ)
    (hE : ∀ j, Supermartingale (E j) ℱ μ) (hJ : Monotone J)
    (hinactive : ∀ n j, J n ≤ j → E j n = 1) :
    Supermartingale (delayedMixture E J) ℱ μ := by
  have he (n : ℕ) : delayedMixture E J n = fixedPriorMixture E (J n) n := by
    funext ω
    exact (fixedPriorMixture_formula E (J n) n ω).symm
  apply supermartingale_nat
  · intro n; rw [he]; exact (fixedPriorMixture_supermartingale E hE (J n)).adapted n
  · intro n; rw [he]; exact (fixedPriorMixture_supermartingale E hE (J n)).integrable n
  · intro n
    rw [he,he]
    have hh := (fixedPriorMixture_supermartingale E hE (J (n+1))).condExp_ae_le (Nat.le_succ n)
    rw [fixedPriorMixture_extension E (J n) (J (n+1)) n (hJ (Nat.le_succ n))
      (hinactive n)] at hh
    exact hh

theorem delayedMixture_nonneg (E : ℕ → ℕ → Ω → ℝ) (J : ℕ → ℕ)
    (hE : ∀ j n ω, 0 ≤ E j n ω) (n : ℕ) (ω : Ω) :
    0 ≤ delayedMixture E J n ω := by
  have hsum : 0 ≤ ∑ j ∈ Finset.range (J n), delayedPrior j*E j n ω :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (delayedPrior_pos j).le (hE j n ω))
  unfold delayedMixture
  positivity

theorem delayedMixture_zero (E : ℕ → ℕ → Ω → ℝ) (J : ℕ → ℕ) (hJ : J 0 = 0) :
    delayedMixture E J 0 = 1 := by funext ω; simp [delayedMixture,hJ]; norm_num

theorem delayedMixture_domination (E R : ℕ → ℕ → Ω → ℝ) (J : ℕ → ℕ)
    (hdom : ∀ j n, R j n ≤ᵐ[μ] E j n) (n : ℕ) :
    delayedMixture R J n ≤ᵐ[μ] delayedMixture E J n := by
  have hall := (ae_all_iff).mpr (fun j => hdom j n)
  filter_upwards [hall] with ω hω
  unfold delayedMixture
  gcongr with j hj
  · exact (delayedPrior_pos j).le
  · exact hω j

end
end EvidenceFusion
