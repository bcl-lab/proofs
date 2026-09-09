import GraphMoments

set_option maxHeartbeats 3000000
namespace HubAveraging
noncomputable section
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/- One independent uniform directed-edge choice. On a regular undirected
graph, this has the same state law as a uniform undirected-edge choice. -/
def edgeAverage (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (z : (V → ℝ) → ℝ) (x : V → ℝ) : ℝ :=
  (∑ v, ∑ u ∈ G.neighborFinset v, z (pairUpdate x v u)) / (Fintype.card V*d)

/- Iterated expectation for independent choices with replacement. -/
def edgeResidual (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    ℕ → (V → ℝ) → ℝ
  | 0 => disagreement
  | n+1 => edgeAverage G d (edgeResidual G d n)

theorem pair_disagreement_loss (x : V → ℝ) (v u : V) (hne : v ≠ u) :
    disagreement (pairUpdate x v u) = disagreement x - (x v-x u)^2/2 := by
  have he := pairUpdate_energy x v u hne
  have hl := disagreement_loss x (pairUpdate x v u) (pairUpdate_total x v u hne)
  linarith

omit [DecidableEq V] [Nonempty V] in
theorem directed_difference_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    (∑ v, ∑ u ∈ G.neighborFinset v, (x v-x u)^2) = 2*lapQuadratic G x := by
  have hi (v : V) : (∑ u ∈ G.neighborFinset v, (x v-x u)^2) =
      d*(x v)^2 - 2*x v*neighborTotal G x v + ∑ u ∈ G.neighborFinset v, (x u)^2 := by
    calc
      _ = ∑ u ∈ G.neighborFinset v, ((x v)^2-2*x v*x u+(x u)^2) :=
        sum_congr rfl fun _ _ => by ring
      _ = _ := by simp [sum_add_distrib, sum_sub_distrib, ← mul_sum, hreg, neighborTotal]
  simp_rw [hi]
  rw [sum_add_distrib, sum_sub_distrib, ← mul_sum,
    regular_neighbor_sum G d hreg, lapQuadratic_expansion G d hreg]
  have hm : (∑ v, 2*x v*neighborTotal G x v) = 2*∑ v, x v*neighborTotal G x v := by
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    ring
  rw [hm]
  change d*energy x - 2*(∑ v, x v*neighborTotal G x v) + d*energy x = _
  ring

/- The one-step stochastic identity is derived from the pair-update code. -/
theorem edgeAverage_disagreement (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    edgeAverage G d disagreement x = disagreement x - lapQuadratic G x/(Fintype.card V*d) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hN : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hi (v : V) : (∑ u ∈ G.neighborFinset v, disagreement (pairUpdate x v u)) =
      d*disagreement x - (∑ u ∈ G.neighborFinset v, (x v-x u)^2)/2 := by
    calc
      _ = ∑ u ∈ G.neighborFinset v, (disagreement x - (x v-x u)^2/2) := by
        apply sum_congr rfl
        intro u hu
        exact pair_disagreement_loss x v u (G.ne_of_adj ((G.mem_neighborFinset _ _).mp hu))
      _ = _ := by simp [sum_sub_distrib, ← sum_div, hreg]
  unfold edgeAverage
  simp_rw [hi]
  rw [sum_sub_distrib, ← sum_div, directed_difference_sum G d hreg]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem edgeAverage_mono (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (z w : (V → ℝ) → ℝ) (hzw : ∀ x, z x ≤ w x) (x : V → ℝ) :
    edgeAverage G d z x ≤ edgeAverage G d w x := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro v _
  apply sum_le_sum
  intro u _
  exact hzw _

omit [Nonempty V] in
theorem edgeAverage_scale (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (z : (V → ℝ) → ℝ) (c : ℝ) (x : V → ℝ) :
    edgeAverage G d (fun y => c*z y) x = c*edgeAverage G d z x := by
  unfold edgeAverage
  simp_rw [← mul_sum]
  ring

/- The spectral gap is supplied as its actual Rayleigh (Poincare) inequality,
not as a hypothesis about the random process. The stochastic induction is proved. -/
theorem independent_edge_contraction (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (lambda : ℝ) (hl : lambda ≤ Fintype.card V*d)
    (hgap : ∀ x, lambda*disagreement x ≤ lapQuadratic G x) (n : ℕ) (x : V → ℝ) :
    edgeResidual G d n x ≤ (1-lambda/(Fintype.card V*d))^n * disagreement x := by
  have hden : (0 : ℝ) < Fintype.card V*d := mul_pos
    (by exact_mod_cast Fintype.card_pos) (by exact_mod_cast hd)
  have hc : 0 ≤ 1-lambda/(Fintype.card V*d) := by
    have hh := (div_le_one hden).2 hl
    linarith
  have hstep (y : V → ℝ) : edgeAverage G d disagreement y ≤
      (1-lambda/(Fintype.card V*d))*disagreement y := by
    rw [edgeAverage_disagreement G d hd hreg]
    have hh := div_le_div_of_nonneg_right (hgap y) hden.le
    calc
      _ ≤ disagreement y - lambda*disagreement y/(Fintype.card V*d) := sub_le_sub_left hh _
      _ = _ := by ring
  induction n generalizing x with
  | zero => simp [edgeResidual]
  | succ n ih =>
    calc
      _ ≤ edgeAverage G d (fun y => (1-lambda/(Fintype.card V*d))^n*disagreement y) x :=
        edgeAverage_mono G d _ _ ih x
      _ = (1-lambda/(Fintype.card V*d))^n * edgeAverage G d disagreement x :=
        edgeAverage_scale G d _ _ x
      _ ≤ (1-lambda/(Fintype.card V*d))^n *
          ((1-lambda/(Fintype.card V*d))*disagreement x) :=
        mul_le_mul_of_nonneg_left (hstep x) (pow_nonneg hc n)
      _ = _ := by rw [pow_succ]; ring

end
end HubAveraging
