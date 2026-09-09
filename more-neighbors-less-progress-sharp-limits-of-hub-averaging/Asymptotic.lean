import GapRange
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option maxHeartbeats 4000000
namespace HubAveraging
noncomputable section
open Finset Filter
open scoped Topology
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [Fintype V] [Nonempty V] in
theorem pairUpdate_symmetric (x : V → ℝ) (v u : V) : pairUpdate x v u = pairUpdate x u v := by
  funext z
  simp only [pairUpdate, or_comm, add_comm]

theorem progress_ratio_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 3 ≤ d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u)
    (hattain : spectralGapAtLeast G (tau d)) (lambda : ℝ) (hl : 0 < lambda)
    (hgap : spectralGapAtLeast G lambda) :
    0 ≤ (1-optimalResidual G)/(1-edgeWorstResidual G d d) := by
  have hd0 : 0 < d := by omega
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hN1 : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := V)))
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hmax : lambda ≤ Fintype.card V*d := by
    have hh := bipartite_gap_le_degree G hconn d (by omega) hreg color hc lambda hgap
    nlinarith
  have hx0 : 0 < disagreement (signState color) := by
    rw [bipartite_witness_disagreement G d hd0 hreg color hc]
    exact hN
  have hbound := edge_budget_exponential G hconn d hd0 hreg lambda hmax hgap _ hx0
  have he : Real.exp (-lambda/Fintype.card V) < 1 := by
    have hh := Real.exp_lt_exp.mpr (neg_neg_of_pos (div_pos hl hN))
    simpa [neg_div] using hh
  have hpos : 0 < 1-edgeWorstResidual G d d := by linarith
  have hEq := (exact_bipartite_minimax G hconn d hd hreg color hc hattain).2
  have hr : r d ≤ 1 := by
    have hh := weighted_r_lt_one d (by omega)
    have hn := r_nonneg d
    nlinarith
  have hr1 : 0 ≤ 1-r d := sub_nonneg.mpr hr
  have hnum : 0 ≤ 1-optimalResidual G := by
    rw [hEq]
    have hp : 0 ≤ (8/3 : ℝ)*(1-r d)/Fintype.card V := by positivity
    linarith
  exact div_nonneg hnum hpos.le

/- Corollary 4's limiting assertion for families of actual finite graphs. -/
theorem vanishing_separation {W : ℕ → Type*}
    [∀ n, Fintype (W n)] [∀ n, DecidableEq (W n)] [∀ n, Nonempty (W n)]
    (G : (n : ℕ) → SimpleGraph (W n)) [∀ n, DecidableRel (G n).Adj]
    (d : ℕ → ℕ) (hconn : ∀ n, (G n).Connected) (hd : ∀ n, 3 ≤ d n)
    (hreg : ∀ n v, (G n).degree v = d n)
    (color : (n : ℕ) → W n → Bool)
    (hc : ∀ n v u, (G n).Adj v u → color n v ≠ color n u)
    (hattain : ∀ n, spectralGapAtLeast (G n) (tau (d n)))
    (lambda : ℕ → ℝ) (hl : ∀ n, 0 < lambda n)
    (hgap : ∀ n, spectralGapAtLeast (G n) (lambda n))
    (hdiverge : Tendsto lambda atTop atTop) :
    Tendsto (fun n => (1-optimalResidual (G n))/(1-edgeWorstResidual (G n) (d n) (d n)))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => 4/(3*(1-Real.exp (-(1/2 : ℝ)))*lambda n)) atTop (𝓝 0) := by
    simpa only [div_div] using hdiverge.const_div_atTop (4/(3*(1-Real.exp (-(1/2 : ℝ)))))
  exact squeeze_zero
    (fun n => progress_ratio_nonneg (G n) (hconn n) (d n) (hd n) (hreg n) (color n) (hc n)
      (hattain n) (lambda n) (hl n) (hgap n))
    (fun n => equal_budget_separation_graph (G n) (hconn n) (d n) (hd n) (hreg n) (color n) (hc n)
      (hattain n) (lambda n) (hl n) (hgap n)) hlim

end
end HubAveraging
