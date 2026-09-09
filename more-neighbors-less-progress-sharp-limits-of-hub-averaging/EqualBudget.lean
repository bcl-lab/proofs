import Minimax

set_option maxHeartbeats 4000000
namespace HubAveraging
noncomputable section
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

theorem graph_poincare (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hreg : ∀ v, G.degree v = d)
    (lambda : ℝ) (hgap : spectralGapAtLeast G lambda) (x : V → ℝ) :
    lambda*disagreement x ≤ lapQuadratic G x := by
  let y := centeredState x
  obtain ⟨hE,hF⟩ := hermitian_polynomial_expansion (G.lapMatrix ℝ) (lapHermitian G) y (1/2) 0
  norm_num at hF
  have hb : lambda*energy y ≤ y ⬝ᵥ ((G.lapMatrix ℝ) *ᵥ y) := by
    rw [hE,hF]
    unfold energy
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    by_cases hz : (lapHermitian G).eigenvalues i = 0
    · rw [centered_zero_eigen_coordinates G hconn y (centeredState_total x) i hz]
      simp
    · have hh := mul_le_mul_of_nonneg_left (hgap i hz)
        (sq_nonneg (((star ((lapHermitian G).eigenvectorUnitary : Matrix V V ℝ)) *ᵥ y) i))
      simpa [mul_comm] using hh
  rw [laplacian_matrix] at hb
  change lambda*energy (centeredState x) ≤ lapQuadratic G (centeredState x) at hb
  rw [centeredState_energy,lapQuadratic_centeredState G d hreg] at hb
  exact hb

theorem edgeResidual_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (d n : ℕ) (x : V → ℝ) :
    0 ≤ edgeResidual G d n x := by
  induction n generalizing x with
  | zero => exact disagreement_nonneg x
  | succ n ih =>
    apply div_nonneg _ (by positivity)
    apply sum_nonneg
    intro v _
    apply sum_nonneg
    intro u _
    exact ih _

def edgeWorstResidual (G : SimpleGraph V) [DecidableRel G.Adj] (d n : ℕ) : ℝ :=
  sSup {q | ∃ x : V → ℝ, 0 < disagreement x ∧ q = edgeResidual G d n x/disagreement x}

/- Equation (13), including the physical graph process and a worst-case supremum. -/
theorem edgeWorst_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (lambda : ℝ) (hlmax : lambda ≤ Fintype.card V*d) (hgap : spectralGapAtLeast G lambda)
    (n : ℕ) (x0 : V → ℝ) (hx0 : 0 < disagreement x0) :
    0 ≤ edgeWorstResidual G d n ∧
      edgeWorstResidual G d n ≤ (1-lambda/(Fintype.card V*d))^n := by
  have hb (x : V → ℝ) (hx : 0 < disagreement x) :
      edgeResidual G d n x/disagreement x ≤ (1-lambda/(Fintype.card V*d))^n := by
    apply (div_le_iff₀ hx).2
    exact independent_edge_contraction G d hd hreg lambda hlmax (graph_poincare G hconn d hreg lambda hgap) n x
  have hB : BddAbove {q | ∃ x : V → ℝ, 0 < disagreement x ∧ q = edgeResidual G d n x/disagreement x} := by
    refine ⟨(1-lambda/(Fintype.card V*d))^n, ?_⟩
    rintro q ⟨x,hx,rfl⟩
    exact hb x hx
  constructor
  · have hL : edgeResidual G d n x0/disagreement x0 ≤ edgeWorstResidual G d n :=
      le_csSup hB ⟨x0,hx0,rfl⟩
    exact (div_nonneg (edgeResidual_nonneg G d n x0) hx0.le).trans hL
  · apply csSup_le
    · exact ⟨_, ⟨x0,hx0,rfl⟩⟩
    · rintro q ⟨x,hx,rfl⟩
      exact hb x hx

theorem edge_budget_exponential (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (lambda : ℝ) (hlmax : lambda ≤ Fintype.card V*d) (hgap : spectralGapAtLeast G lambda)
    (x0 : V → ℝ) (hx0 : 0 < disagreement x0) :
    edgeWorstResidual G d d ≤ Real.exp (-lambda/Fintype.card V) := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : lambda/(Fintype.card V*d) ≤ 1 := (div_le_one (mul_pos hN hdR)).2 hlmax
  have he := independent_budget_exponential (lambda/(Fintype.card V*d)) d ht
  have harg : -(d : ℝ)*(lambda/(Fintype.card V*d)) = -lambda/Fintype.card V := by field_simp; ring
  rw [harg] at he
  exact (edgeWorst_bound G hconn d hd hreg lambda hlmax hgap d x0 hx0).2.trans he

omit [DecidableEq V] [Nonempty V] in
theorem bipartite_witness_disagreement (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u) :
    disagreement (signState color) = Fintype.card V := by
  have hopp := fun v u (hu : G.Adj v u) => signState_opposite color v u (hc v u hu)
  rw [disagreement_of_total_zero _ (regular_bipartition_total_zero G d hd hreg _ hopp),
    sign_energy _ (signState_values color)]

/- Equation (14) for actual worst-case residuals. The parameter lambda is any
certified positive lower bound on the graph's nonzero Laplacian spectrum. -/
theorem equal_budget_separation (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 3 ≤ d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u)
    (hattain : spectralGapAtLeast G (tau d)) (lambda : ℝ) (hl : 0 < lambda)
    (hgap : spectralGapAtLeast G lambda) (hhalf : lambda/Fintype.card V ≤ 1/2) :
    (1-optimalResidual G)/(1-edgeWorstResidual G d d) ≤
      4/(3*(1-Real.exp (-(1/2 : ℝ)))*lambda) := by
  have hd0 : 0 < d := by omega
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hmax : lambda ≤ Fintype.card V*d := by
    have hh := (div_le_iff₀ hN).mp hhalf
    nlinarith
  have hx0 : 0 < disagreement (signState color) := by
    rw [bipartite_witness_disagreement G d hd0 hreg color hc]
    exact hN
  have he := edge_budget_exponential G hconn d hd0 hreg lambda hmax hgap _ hx0
  have hp : 0 < 1-Real.exp (-(lambda/Fintype.card V)) := by
    have hh := Real.exp_lt_exp.mpr (neg_neg_of_pos (div_pos hl hN))
    simp only [Real.exp_zero] at hh
    linarith
  have heq : -lambda/Fintype.card V = -(lambda/Fintype.card V) := by ring
  rw [heq] at he
  have hlow : 1-Real.exp (-(lambda/Fintype.card V)) ≤ 1-edgeWorstResidual G d d := by linarith
  have hE := (exact_bipartite_minimax G hconn d hd hreg color hc hattain).2
  have hr : r d ≤ 1 := by
    have hh := weighted_r_lt_one d (by omega)
    have hn := r_nonneg d
    nlinarith
  have hr1 : 0 ≤ 1-r d := sub_nonneg.mpr hr
  have hpos : 0 ≤ ((8/3 : ℝ)*(1-r d))/Fintype.card V := by positivity
  have hprog : 1-optimalResidual G = ((8/3 : ℝ)*(1-r d))/Fintype.card V := by rw [hE]; ring
  rw [hprog]
  calc
    _ ≤ (((8/3 : ℝ)*(1-r d))/Fintype.card V)/(1-Real.exp (-(lambda/Fintype.card V))) :=
      div_le_div_of_nonneg_left hpos hp hlow
    _ = 8*(1-r d)/(3*Fintype.card V*(1-Real.exp (-(lambda/Fintype.card V)))) := by field_simp
    _ ≤ _ := separation_ratio_bound _ _ _ hN hl (r_nonneg d) hhalf

end
end HubAveraging
