import GraphMoments

set_option maxHeartbeats 3000000
namespace HubAveraging
noncomputable section
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

def closedBlock (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset V :=
  insert v (G.neighborFinset v)

def sameDegree (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → Bool) (v : V) : ℕ :=
  ((G.neighborFinset v).filter (fun u => color u = color v)).card

def cutCap (G : SimpleGraph V) [DecidableRel G.Adj] (color : V → Bool) (v : V) : ℝ :=
  4*((sameDegree G color v : ℝ)+1)*((G.degree v : ℝ)-sameDegree G color v)/((G.degree v : ℝ)+1)

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem sign_relative (color : V → Bool) (v u : V) :
    signState color u = if color u = color v then signState color v else -signState color v := by
  cases hv : color v <;> cases hu : color u <;> simp [signState, hv, hu]

omit [Fintype V] [DecidableEq V] [Nonempty V] in
theorem sign_block_sum (s : Finset V) (color : V → Bool) (v : V) :
    (∑ u ∈ s, signState color u) =
      signState color v * (2*((s.filter (fun u => color u = color v)).card : ℝ)-s.card) := by
  have hc := filter_card_add_filter_neg_card_eq_card (s := s) (fun u => color u = color v)
  have hcR : ((s.filter (fun u => color u = color v)).card : ℝ) +
      ((s.filter (fun u => ¬color u = color v)).card : ℝ) = s.card := by exact_mod_cast hc
  have he : (∑ u ∈ s, signState color u) =
      ∑ u ∈ s, (if color u = color v then signState color v else -signState color v) :=
    sum_congr rfl fun u _ => sign_relative color v u
  rw [he, sum_ite]
  simp only [sum_const, nsmul_eq_mul]
  rw [← hcR]
  ring

omit [Nonempty V] in
theorem closedBlock_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (closedBlock G v).card = G.degree v+1 := by
  simp [closedBlock, G.not_mem_neighborFinset_self]

omit [Nonempty V] in
theorem closedBlock_same_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    ((closedBlock G v).filter (fun u => color u = color v)).card = sameDegree G color v+1 := by
  simp [closedBlock, sameDegree, filter_insert, G.not_mem_neighborFinset_self]

omit [Nonempty V] in
theorem sign_closedBlock_sum_sq (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (∑ u ∈ closedBlock G v, signState color u)^2 =
      (2*((sameDegree G color v : ℝ)+1)-((G.degree v : ℝ)+1))^2 := by
  rw [sign_block_sum _ color v, closedBlock_same_card, closedBlock_card, mul_pow]
  have hs : (signState color v)^2 = 1 := by
    rcases signState_values color v with h | h <;> norm_num [h]
  simp [hs]

omit [Nonempty V] in
theorem sign_closedBlock_energy (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) :
    (∑ u ∈ closedBlock G v, (signState color u)^2) = (G.degree v : ℝ)+1 := by
  have hs (u : V) : (signState color u)^2 = 1 := by
    rcases signState_values color u with h | h <;> norm_num [h]
  simp [hs, closedBlock_card]

/- Proposition 5's pointwise geometric cap on actual closed neighborhoods.
All sign counts are calculated from the graph and the coloring. -/
omit [Nonempty V] in
theorem graph_cut_energy_cap (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (v : V) (y : V → ℝ)
    (hpres : (∑ u ∈ closedBlock G v, y u) = ∑ u ∈ closedBlock G v, signState color u)
    (hoff : ∀ u, u ∉ closedBlock G v → y u = signState color u) :
    energy (signState color) - energy y ≤ cutCap G color v := by
  have hs : 0 < (closedBlock G v).card := by rw [closedBlock_card]; omega
  have hb := sum_preserving_block_bound (closedBlock G v) (signState color) y hs hpres
  rw [sign_closedBlock_energy, sign_closedBlock_sum_sq, closedBlock_card] at hb
  unfold energy
  rw [supported_energy_loss (closedBlock G v) (signState color) y (fun u hu => (hoff u hu).symm)]
  rw [sign_closedBlock_energy]
  calc
    _ ≤ _ := hb
    _ = cutCap G color v := by
      unfold cutCap
      push_cast
      field_simp
      ring

omit [DecidableEq V] [Nonempty V] in
theorem supported_total (s : Finset V) (x y : V → ℝ)
    (hpres : (∑ u ∈ s, y u) = ∑ u ∈ s, x u)
    (hoff : ∀ u, u ∉ s → y u = x u) : total y = total x := by
  have he : (∑ u ∈ s, (y u-x u)) = ∑ u, (y u-x u) := by
    apply sum_subset (subset_univ _)
    intro u _ hu
    rw [hoff u hu, sub_self]
  rw [sum_sub_distrib, sum_sub_distrib, hpres, sub_self] at he
  exact (sub_eq_zero.mp he.symm)

/- The cap applies to arbitrary real outputs, without assuming they are
averages or convex combinations. Balance is the zero-sum sign condition. -/
theorem graph_cut_residual (G : SimpleGraph V) [DecidableRel G.Adj]
    (color : V → Bool) (hbal : total (signState color) = 0)
    (v : V) (y : V → ℝ)
    (hpres : (∑ u ∈ closedBlock G v, y u) = ∑ u ∈ closedBlock G v, signState color u)
    (hoff : ∀ u, u ∉ closedBlock G v → y u = signState color u) :
    max 0 (1-cutCap G color v/Fintype.card V) ≤ disagreement y/Fintype.card V := by
  have hz := (supported_total (closedBlock G v) (signState color) y hpres hoff).trans hbal
  have he := graph_cut_energy_cap G color v y hpres hoff
  rw [sign_energy _ (signState_values color)] at he
  rw [disagreement_of_total_zero y hz]
  apply cut_residual_ratio _ _ _ (by exact_mod_cast Fintype.card_pos)
  · exact sum_nonneg fun _ _ => sq_nonneg _
  · exact he

end
end HubAveraging
