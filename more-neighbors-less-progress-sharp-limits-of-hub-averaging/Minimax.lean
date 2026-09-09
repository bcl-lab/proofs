import GraphSpectral
import UniformPolicy

set_option maxHeartbeats 4000000
namespace HubAveraging
noncomputable section
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def centeredState (x : V → ℝ) : V → ℝ := fun v => x v-total x/Fintype.card V

omit [DecidableEq V] in
theorem centeredState_total (x : V → ℝ) : total (centeredState x) = 0 := by
  have hN : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold total centeredState
  rw [sum_sub_distrib]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp
  unfold total
  ring

omit [DecidableEq V] [Nonempty V] in
theorem centeredState_energy (x : V → ℝ) : energy (centeredState x) = disagreement x := rfl

omit [DecidableEq V] [Nonempty V] in
theorem laplacian_centeredState (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) : laplacian G (centeredState x) = laplacian G x := by
  ext v
  unfold laplacian centeredState neighborTotal
  rw [sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree]
  ring

omit [DecidableEq V] [Nonempty V] in
theorem laplacian_total (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) : total (laplacian G x) = 0 := by
  unfold total laplacian neighborTotal
  simp_rw [hreg]
  rw [sum_sub_distrib, ← mul_sum, regular_neighbor_sum G d hreg]
  simp [total]

omit [DecidableEq V] [Nonempty V] in
theorem lapQuadratic_centeredState (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    lapQuadratic G (centeredState x) = lapQuadratic G x := by
  unfold lapQuadratic
  rw [laplacian_centeredState]
  simp only [centeredState, sub_mul, sum_sub_distrib, ← mul_sum]
  have ht := laplacian_total G d hreg x
  unfold total at ht
  rw [ht, mul_zero, sub_zero]

/- The graph spectral inequality for every input, with its mean removed in Lean. -/
theorem graph_threshold_all (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 2 ≤ d) (hreg : ∀ v, G.degree v = d)
    (hgap : spectralGapAtLeast G (tau d)) (x : V → ℝ) :
    (8/3 : ℝ)*(1-r d)*disagreement x ≤
      2*a d*lapQuadratic G x-gamma d*energy (laplacian G x) := by
  have hb := centered_graph_threshold G hconn d hd hreg hgap (centeredState x) (centeredState_total x)
  rw [disagreement_of_total_zero _ (centeredState_total x), centeredState_energy,
    lapQuadratic_centeredState G d hreg, laplacian_centeredState] at hb
  exact hb

theorem action_energy_disagreement_loss {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : V → ℝ) (s : SweepAction G) :
    energy x-energy (actionState x s) = disagreement x-disagreement (actionState x s) := by
  have hh : s.1 ∉ actionOrder s := by rw [actionOrder_mem]; exact G.loopless _
  exact (disagreement_loss x (actionState x s) (networkSweep_total x s.1 (actionOrder s) hh)).symm

theorem uniform_expected_residual (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    expected (uniformPolicy G x) (fun s => disagreement (actionState x s)) =
      disagreement x-(2*a d*lapQuadratic G x-gamma d*energy (laplacian G x))/Fintype.card V := by
  have he := uniform_graph_operator G d hd hreg x
  simp_rw [action_energy_disagreement_loss] at he
  unfold expected at he ⊢
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, (uniformPolicy G x).mass, one_mul] at he
  linarith

theorem uniform_ratio_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 2 ≤ d) (hreg : ∀ v, G.degree v = d)
    (hgap : spectralGapAtLeast G (tau d)) (x : V → ℝ) (hx : 0 < disagreement x) :
    policyRatio (uniformPolicy G) x ≤ 1-(8/3 : ℝ)*(1-r d)/Fintype.card V := by
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  unfold policyRatio
  rw [uniform_expected_residual G d (by omega) hreg]
  apply (div_le_iff₀ hx).2
  have hb := div_le_div_of_nonneg_right (graph_threshold_all G hconn d hd hreg hgap x) hN.le
  calc
    _ ≤ disagreement x-((8/3 : ℝ)*(1-r d)*disagreement x)/Fintype.card V := sub_le_sub_left hb _
    _ = _ := by ring

/- Theorem 3, including exact attainment and the infimum over all policies.
The spectral hypothesis is on the actual nonzero Laplacian eigenvalues. -/
theorem exact_bipartite_minimax (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 3 ≤ d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u)
    (hgap : spectralGapAtLeast G (tau d)) :
    worstResidual (uniformPolicy G) = 1-(8/3 : ℝ)*(1-r d)/Fintype.card V ∧
    optimalResidual G = 1-(8/3 : ℝ)*(1-r d)/Fintype.card V := by
  have hd0 : 0 < d := by omega
  have hopp := fun v u (hu : G.Adj v u) => signState_opposite color v u (hc v u hu)
  have hx : 0 < disagreement (signState color) := by
    rw [disagreement_of_total_zero _ (regular_bipartition_total_zero G d hd0 hreg _ hopp),
      sign_energy _ (signState_values color)]
    exact_mod_cast Fintype.card_pos
  have hU : worstResidual (uniformPolicy G) ≤ 1-(8/3 : ℝ)*(1-r d)/Fintype.card V := by
    apply csSup_le
    · exact ⟨policyRatio (uniformPolicy G) (signState color), ⟨signState color,hx,rfl⟩⟩
    · rintro q ⟨x,hx,rfl⟩
      exact uniform_ratio_upper G hconn d (by omega) hreg hgap x hx
  have hEq : worstResidual (uniformPolicy G) = 1-(8/3 : ℝ)*(1-r d)/Fintype.card V :=
    le_antisymm hU (bipartite_policy_lower_bound G d hd0 hreg color hc _)
  refine ⟨hEq, le_antisymm ?_ (bipartite_minimax_lower_bound G d hd0 hreg color hc)⟩
  calc
    optimalResidual G ≤ worstResidual (uniformPolicy G) := by
      apply csInf_le
      · refine ⟨1-(8/3 : ℝ)*(1-r d)/Fintype.card V, ?_⟩
        rintro q ⟨P,rfl⟩
        exact bipartite_policy_lower_bound G d hd0 hreg color hc P
      · exact ⟨uniformPolicy G,rfl⟩
    _ = _ := hEq

end
end HubAveraging
