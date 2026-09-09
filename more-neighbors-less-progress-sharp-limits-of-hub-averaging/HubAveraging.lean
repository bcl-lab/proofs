import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
Formal verification of explicit proof components from
"More neighbors, less progress: Sharp limits of hub averaging".

The graph-to-operator and spectral-decomposition bridges are NOT assumed
as global axioms. Where needed, they appear as named theorem hypotheses.
See the accompanying coverage report before describing the whole paper
as formally verified.
-/

set_option maxHeartbeats 2000000

namespace HubAveraging
noncomputable section
open Finset

/-- Squared energy on a list of leaf values. -/
def leafEnergy (xs : List ℝ) : ℝ := (xs.map (fun x => x ^ 2)).sum

/-- The physical sweep: the current hub is averaged with the next leaf;
that leaf is then left unchanged while the remaining leaves are visited. -/
def sweep (h : ℝ) : List ℝ → ℝ × List ℝ
  | [] => (h, [])
  | l :: ls =>
    let q := (h + l) / 2
    let z := sweep q ls
    (z.1, q :: z.2)

/-- Sum of the actual pairwise losses along a sweep. -/
def sweepLoss (h : ℝ) : List ℝ → ℝ
  | [] => 0
  | l :: ls => (h - l) ^ 2 / 2 + sweepLoss ((h + l) / 2) ls

theorem pair_energy_loss (h l : ℝ) :
    h ^ 2 + l ^ 2 - 2 * ((h + l) / 2) ^ 2 = (h - l) ^ 2 / 2 := by
  ring

theorem pair_preserves_sum (h l : ℝ) :
    (h + l) / 2 + (h + l) / 2 = h + l := by ring

theorem sweep_preserves_sum (h : ℝ) (ls : List ℝ) :
    (sweep h ls).1 + (sweep h ls).2.sum = h + ls.sum := by
  induction ls generalizing h with
  | nil => simp [sweep]
  | cons l ls ih =>
    have hi := ih ((h + l) / 2)
    simp only [sweep, List.sum_cons] at *
    linarith

theorem sweep_energy_loss (h : ℝ) (ls : List ℝ) :
    h ^ 2 + leafEnergy ls -
      ((sweep h ls).1 ^ 2 + leafEnergy (sweep h ls).2) = sweepLoss h ls := by
  induction ls generalizing h with
  | nil => simp [sweep, sweepLoss, leafEnergy]
  | cons l ls ih =>
    have hi := ih ((h + l) / 2)
    have hp := pair_energy_loss h l
    simp only [sweep, sweepLoss, leafEnergy, List.map_cons, List.sum_cons] at *
    linarith

/-- General closed form for a hub facing equal, previously untouched leaves. -/
theorem equal_leaf_sweep_loss (h l : ℝ) (d : ℕ) :
    sweepLoss h (List.replicate d l) =
      (2 / 3 : ℝ) * (h - l) ^ 2 * (1 - (1 / 4 : ℝ) ^ d) := by
  induction d generalizing h with
  | zero => simp [sweepLoss]
  | succ d ih =>
    simp only [List.replicate_succ, sweepLoss, ih, pow_succ]
    ring

/-- Equation 11, proved from the physical sequential sweep for every degree. -/
theorem bipartition_witness_loss (d : ℕ) :
    1 ^ 2 + leafEnergy (List.replicate d (-1)) -
      ((sweep 1 (List.replicate d (-1))).1 ^ 2 +
        leafEnergy (sweep 1 (List.replicate d (-1))).2) =
      (8 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ d) := by
  rw [sweep_energy_loss, equal_leaf_sweep_loss]
  ring

/-- The sign-reversed bipartition has exactly the same loss. -/
theorem reversed_bipartition_witness_loss (d : ℕ) :
    sweepLoss (-1) (List.replicate d 1) =
      (8 / 3 : ℝ) * (1 - (1 / 4 : ℝ) ^ d) := by
  rw [equal_leaf_sweep_loss]
  ring

/-- Randomizing finite outcomes cannot change a common witness value.
The weights can be the pushforward of any random seed distribution. -/
theorem common_witness_expectation {ι : Type*} [Fintype ι]
    (p y : ι → ℝ) (C : ℝ) (hp : ∑ i, p i = 1)
    (hy : ∀ i, y i = C) : (∑ i, p i * y i) = C := by
  simp_rw [hy]
  rw [← Finset.sum_mul, hp, one_mul]

/-- Finite expectations preserve a pointwise lower bound. -/
theorem expectation_lower_bound {ι : Type*} [Fintype ι]
    (p y : ι → ℝ) (C : ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (hy : ∀ i, C ≤ y i) :
    C ≤ ∑ i, p i * y i := by
  calc
    C = ∑ i, p i * C := by rw [← Finset.sum_mul, hp, one_mul]
    _ ≤ ∑ i, p i * y i := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hy i) (hp0 i))

/-- Finite-outcome version of the policy lower bound once the common
physical witness energies have been identified. -/
theorem policy_witness_ratio {ι : Type*} [Fintype ι]
    (p y : ι → ℝ) (N C : ℝ) (hN : 0 < N)
    (hp : ∑ i, p i = 1) (hy : ∀ i, y i = N - C) :
    (∑ i, p i * y i) / N = 1 - C / N := by
  rw [common_witness_expectation p y (N - C) hp hy]
  field_simp

/-- Coefficients use real division and natural-number exponents throughout. -/
def r (d : ℕ) : ℝ := (1 / 4 : ℝ) ^ d
def alpha (d : ℕ) : ℝ :=
  (3 * (d : ℝ)^2 - 7*d + 6 - 2*(d+3)*r d) / (9*d*(d-1))
def beta (d : ℕ) : ℝ := ((d : ℝ)-2+2*(d+1)*r d)/(3*d)
def a (d : ℕ) : ℝ := 1 - alpha d
def b (d : ℕ) : ℝ := 1 - beta d
def gamma (d : ℕ) : ℝ := (((d : ℝ)+1)*a d-b d)/(d*(d+1))
def f (d : ℕ) (x : ℝ) : ℝ := 2*a d*x-gamma d*x^2
def tau (d : ℕ) : ℝ := 2*d*b d/(((d : ℝ)+1)*a d-b d)

theorem r_nonneg (d : ℕ) : 0 ≤ r d := by unfold r; positivity

theorem weighted_r_lt_one (d : ℕ) (hd : 2 ≤ d) :
    (3*(d : ℝ)+1)*r d < 1 := by
  induction d, hd using Nat.le_induction with
  | base => norm_num [r]
  | succ n hn ih =>
    have hr := r_nonneg n
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [r, pow_succ, Nat.cast_add, Nat.cast_one] at *
    nlinarith

theorem coefficient_bounds (d : ℕ) (hd : 2 ≤ d) :
    0 ≤ beta d ∧ beta d < alpha d ∧ alpha d < (1 / 3 : ℝ) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hdm : (0 : ℝ) < (d : ℝ)-1 := by linarith
  have hr := r_nonneg d
  have hwr := weighted_r_lt_one d hd
  have hab : alpha d - beta d =
      2*(1-(3*(d : ℝ)+1)*r d)/(9*((d : ℝ)-1)) := by
    unfold alpha beta
    field_simp
    ring
  have ha3 : (1 / 3 : ℝ) - alpha d =
      (4*(d : ℝ)-6+2*((d : ℝ)+3)*r d)/(9*d*((d : ℝ)-1)) := by
    unfold alpha
    field_simp
    ring
  constructor
  · unfold beta
    apply div_nonneg
    · have hdm2 : 0 ≤ (d : ℝ)-2 := by linarith
      positivity
    · positivity
  constructor
  · have hnum : 0 < 1-(3*(d : ℝ)+1)*r d := by linarith
    have : 0 < alpha d - beta d := by rw [hab]; positivity
    linarith
  · have hbase : 0 < 4*(d : ℝ)-6 := by linarith
    have : 0 < (1 / 3 : ℝ) - alpha d := by rw [ha3]; positivity
    linarith

theorem gamma_pos (d : ℕ) (hd : 2 ≤ d) : 0 < gamma d := by
  obtain ⟨hb0, hba, ha3⟩ := coefficient_bounds d hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : (2 / 3 : ℝ) < a d := by unfold a; linarith
  have hb : b d ≤ 1 := by unfold b; linarith
  unfold gamma
  apply div_pos
  · nlinarith
  · positivity

theorem spectral_factorization (d : ℕ) (x : ℝ) :
    f d x - f d (2*d) =
      (x-2*d)*(2*a d-gamma d*(x+2*d)) := by
  unfold f
  ring

theorem bipartition_spectral_value (d : ℕ) (hd : 0 < d) :
    f d (2*d) = (8 / 3 : ℝ)*(1-r d) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hd1 : (d : ℝ)+1 ≠ 0 := by positivity
  unfold f gamma b beta
  field_simp
  ring

/-- Threshold identity; the local coefficients remain explicit. -/
theorem threshold_identity (d : ℕ) (hd : 2 ≤ d) :
    gamma d * (tau d + 2*d) = 2*a d := by
  have hg := gamma_pos d hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : ((d : ℝ)+1)*a d-b d ≠ 0 := by
    intro he
    simp [gamma, he] at hg
  unfold gamma tau
  field_simp
  ring

theorem spectral_threshold (d : ℕ) (hd : 2 ≤ d) (x : ℝ)
    (hx : tau d ≤ x) (hx2 : x ≤ 2*d) :
    (8 / 3 : ℝ)*(1-r d) ≤ f d x := by
  have hg := gamma_pos d hd
  have ht := threshold_identity d hd
  have he := spectral_factorization d x
  have hprod : 0 ≤ (x-2*d)*(2*a d-gamma d*(x+2*d)) := by
    apply mul_nonneg_of_nonpos_of_nonpos
    · linarith
    · nlinarith
  rw [bipartition_spectral_value d (by omega)] at he
  linarith

/-- The scalar spectral conclusion, given a nonnegative spectral energy
expansion. This theorem does not itself construct a graph eigenbasis. -/
theorem spectral_energy_bound {ι : Type*} [Fintype ι]
    (d : ℕ) (hd : 2 ≤ d) (lambda w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hl : ∀ i, tau d ≤ lambda i)
    (hu : ∀ i, lambda i ≤ 2*d) :
    ((8 / 3 : ℝ)*(1-r d)) * (∑ i, w i) ≤ ∑ i, w i*f d (lambda i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (spectral_threshold d hd (lambda i) (hl i) (hu i)) (hw i)
  nlinarith

/-- The hub-versus-leaves coefficient comes from a concrete physical sweep. -/
theorem beta_from_physical_sweep (d : ℕ) (hd : 0 < d) :
    1 - sweepLoss (d : ℝ) (List.replicate d (-1)) /
      ((d : ℝ)*(d+1)) = beta d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [equal_leaf_sweep_loss]
  unfold beta r
  field_simp
  ring

/-- Squared column norm for the initial unit hub. -/
theorem unit_hub_column_norm (d : ℕ) :
    (sweep 1 (List.replicate d 0)).1^2 +
      leafEnergy (sweep 1 (List.replicate d 0)).2 = (1+2*r d)/3 := by
  have he := sweep_energy_loss 1 (List.replicate d 0)
  rw [equal_leaf_sweep_loss] at he
  simp [leafEnergy, r] at *
  linarith

/-- The two local coefficients obey the trace equation used in Lemma 1. -/
theorem coefficient_trace_identity (d : ℕ) (hd : 2 ≤ d) :
    1 + beta d + ((d : ℝ)-1)*alpha d = (3*d+5+4*r d)/9 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hdm0 : (d : ℝ)-1 ≠ 0 := by linarith
  unfold alpha beta
  field_simp [hd0, hdm0]
  ring

/-- Exact small-degree values used for the complete bipartite example. -/
theorem degree_three_values : a 3 = (25/32 : ℝ) ∧ b 3 = (7/8 : ℝ) := by
  norm_num [a,b,alpha,beta,r]

/-- The sufficient spectral threshold is at most d for every d at least 3. -/
theorem threshold_le_degree (d : ℕ) (hd : 3 ≤ d) : tau d ≤ d := by
  obtain ⟨hb0, hba, ha3⟩ := coefficient_bounds d (by omega)
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : (2/3 : ℝ) < a d := by unfold a; linarith
  have hb : b d ≤ 1 := by unfold b; linarith
  have hcoef : 3*b d ≤ ((d : ℝ)+1)*a d := by
    by_cases heq : d = 3
    · subst d
      norm_num [a,b,alpha,beta,r]
    · have h4 : (4 : ℝ) ≤ d := by exact_mod_cast (show 4 ≤ d by omega)
      nlinarith
  have hD : 0 < ((d : ℝ)+1)*a d-b d := by nlinarith
  unfold tau
  apply (div_le_iff₀ hD).2
  nlinarith

/-- Every visiting order on the opposite-sign witness has the same loss.
Distinctness is immaterial for this list-level identity; a physical graph
sweep must additionally identify these entries with distinct neighbors. -/
theorem all_opposite_orders_loss {ι : Type*} (state : ι → ℝ)
    (v : ι) (order : List ι) (d : ℕ) (hlen : order.length = d)
    (hsign : state v = 1 ∨ state v = -1)
    (hopposite : ∀ u ∈ order, state u = -(state v)) :
    sweepLoss (state v) (order.map state) = (8/3 : ℝ)*(1-r d) := by
  have hm : order.map state = List.replicate order.length (-(state v)) :=
    List.map_eq_replicate_iff.mpr hopposite
  rw [hm, hlen, equal_leaf_sweep_loss]
  rcases hsign with h | h <;> rw [h] <;> unfold r <;> ring

/-- Arbitrary finite randomized hub and order selection, including weights
chosen after observing the witness, has exactly the same expected loss. -/
theorem all_selectors_expected_loss {ι Ω : Type*} [Fintype Ω]
    (state : ι → ℝ) (hub : Ω → ι) (order : Ω → List ι)
    (p : Ω → ℝ) (d : ℕ) (hp : ∑ o, p o = 1)
    (hlen : ∀ o, (order o).length = d)
    (hsign : ∀ o, state (hub o) = 1 ∨ state (hub o) = -1)
    (hopposite : ∀ o u, u ∈ order o → state u = -(state (hub o))) :
    (∑ o, p o*sweepLoss (state (hub o)) ((order o).map state)) =
      (8/3 : ℝ)*(1-r d) := by
  apply common_witness_expectation p _ _ hp
  intro o
  exact all_opposite_orders_loss state (hub o) (order o) d (hlen o) (hsign o) (hopposite o)

end
end HubAveraging
