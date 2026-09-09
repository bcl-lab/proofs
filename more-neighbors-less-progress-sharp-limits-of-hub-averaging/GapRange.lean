import EqualBudget
import GraphCut

set_option maxHeartbeats 4000000
namespace HubAveraging
noncomputable section
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def contrastState (u w : V) : V → ℝ := fun z => if z = u then 1 else if z = w then -1 else 0

omit [Nonempty V] in
theorem contrast_total (u w : V) (huw : u ≠ w) : total (contrastState u w) = 0 := by
  calc
    _ = ∑ z ∈ ({u,w} : Finset V), contrastState u w z := by
      symm
      apply sum_subset (subset_univ _)
      intro z _ hz
      simp only [mem_insert,mem_singleton,not_or] at hz
      simp [contrastState,hz.1,hz.2]
    _ = _ := by simp [contrastState,huw,Ne.symm huw]

omit [Nonempty V] in
theorem contrast_energy (u w : V) (huw : u ≠ w) : energy (contrastState u w) = 2 := by
  calc
    _ = ∑ z ∈ ({u,w} : Finset V), (contrastState u w z)^2 := by
      symm
      apply sum_subset (subset_univ _)
      intro z _ hz
      simp only [mem_insert,mem_singleton,not_or] at hz
      simp [contrastState,hz.1,hz.2]
    _ = _ := by norm_num [contrastState,huw,Ne.symm huw]

omit [Nonempty V] in
theorem contrast_neighbor_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (v u w : V) (hu : ¬G.Adj v u) (hw : ¬G.Adj v w) :
    neighborTotal G (contrastState u w) v = 0 := by
  apply sum_eq_zero
  intro z hz
  have hzu : z ≠ u := fun he => hu (he ▸ (G.mem_neighborFinset _ _).mp hz)
  have hzw : z ≠ w := fun he => hw (he ▸ (G.mem_neighborFinset _ _).mp hz)
  simp [contrastState,hzu,hzw]

omit [Nonempty V] in
theorem contrast_quadratic (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (u w : V)
    (huw : u ≠ w) (hnot : ¬G.Adj u w) : lapQuadratic G (contrastState u w) = 2*d := by
  have hu := contrast_neighbor_zero G u u w (G.loopless u) hnot
  have hw := contrast_neighbor_zero G w u w (by simpa [G.adj_comm] using hnot) (G.loopless w)
  have hc : (∑ z, contrastState u w z*neighborTotal G (contrastState u w) z) = 0 := by
    calc
      _ = ∑ z ∈ ({u,w} : Finset V), contrastState u w z*neighborTotal G (contrastState u w) z := by
        symm
        apply sum_subset (subset_univ _)
        intro z _ hz
        simp only [mem_insert,mem_singleton,not_or] at hz
        simp [contrastState,hz.1,hz.2]
      _ = _ := by simp [huw,hu,hw]
  rw [lapQuadratic_expansion G d hreg, contrast_energy u w huw, hc]
  ring

theorem bipartite_gap_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 2 ≤ d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u)
    (lambda : ℝ) (hgap : spectralGapAtLeast G lambda) : lambda ≤ d := by
  let v : V := Classical.arbitrary V
  have hn : 1 < (G.neighborFinset v).card := by rw [G.card_neighborFinset_eq_degree,hreg]; omega
  obtain ⟨u,w,hu,hw,huw⟩ := one_lt_card_iff.mp hn
  have hcu := hc v u ((G.mem_neighborFinset _ _).mp hu)
  have hcw := hc v w ((G.mem_neighborFinset _ _).mp hw)
  have hsame : color u = color w := by
    cases hv : color v <;> cases hu' : color u <;> cases hw' : color w <;> simp_all
  have hnot : ¬G.Adj u w := fun hh => (hc u w hh) hsame
  have hb := graph_poincare G hconn d hreg lambda hgap (contrastState u w)
  rw [disagreement_of_total_zero _ (contrast_total u w huw), contrast_energy u w huw,
    contrast_quadratic G d hreg u w huw hnot] at hb
  linarith

omit [DecidableEq V] in
theorem bipartite_degree_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u) :
    2*(d : ℝ) ≤ Fintype.card V := by
  let v : V := Classical.arbitrary V
  let p := univ.filter (fun u => color u = color v)
  let q := univ.filter (fun u => ¬color u = color v)
  have hz := regular_bipartition_total_zero G d hd hreg (signState color)
    (fun v u hu => signState_opposite color v u (hc v u hu))
  have hs := sign_block_sum (univ : Finset V) color v
  change total (signState color) = signState color v*(2*(p.card : ℝ)-Fintype.card V) at hs
  rw [hz] at hs
  have hp : 2*(p.card : ℝ) = Fintype.card V := by
    rcases signState_values color v with h | h <;> rw [h] at hs <;> linarith
  have ht : (p.card : ℝ)+(q.card : ℝ) = Fintype.card V := by
    exact_mod_cast (filter_card_add_filter_neg_card_eq_card (s := univ) (fun u => color u = color v))
  have hsub : G.neighborFinset v ⊆ q := by
    intro u hu
    exact mem_filter.mpr ⟨mem_univ _,Ne.symm (hc v u ((G.mem_neighborFinset _ _).mp hu))⟩
  have hcard := card_le_card hsub
  rw [G.card_neighborFinset_eq_degree,hreg] at hcard
  have hR : (d : ℝ) ≤ q.card := by exact_mod_cast hcard
  linarith

/- The spectral-gap range used in equation (14) is proved from the graph. -/
theorem bipartite_gap_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 2 ≤ d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u)
    (lambda : ℝ) (hgap : spectralGapAtLeast G lambda) : lambda/Fintype.card V ≤ 1/2 := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hN).2
  have h1 := bipartite_gap_le_degree G hconn d hd hreg color hc lambda hgap
  have h2 := bipartite_degree_half G d (by omega) hreg color hc
  linarith

theorem equal_budget_separation_graph (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 3 ≤ d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u)
    (hattain : spectralGapAtLeast G (tau d)) (lambda : ℝ) (hl : 0 < lambda)
    (hgap : spectralGapAtLeast G lambda) :
    (1-optimalResidual G)/(1-edgeWorstResidual G d d) ≤
      4/(3*(1-Real.exp (-(1/2 : ℝ)))*lambda) :=
  equal_budget_separation G hconn d hd hreg color hc hattain lambda hl hgap
    (bipartite_gap_half G hconn d (by omega) hreg color hc lambda hgap)

end
end HubAveraging
