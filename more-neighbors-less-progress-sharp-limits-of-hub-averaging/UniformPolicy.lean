import PermutationMean
import GraphMoments

set_option maxHeartbeats 5000000
namespace HubAveraging
noncomputable section
open Finset

theorem localFormula_b (n : ℕ) (hn : 0 < n) (h t q : ℝ) :
    localFormula n h t q = a n*(q-t^2/n) + b n*n/(n+1)*(h-t/n)^2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hnp : (n : ℝ)+1 ≠ 0 := by positivity
  unfold localFormula b beta
  field_simp
  ring

/-- The exact local S and H identity for literal uniform permutations. -/
theorem uniform_permutation_SH (n : ℕ) (hn : 0 < n) (h : ℝ) (x : Fin n → ℝ) :
    permutationLoss n h x =
      a n*(∑ i, (x i-(∑ j, x j)/n)^2) +
      b n*n/(n+1)*(h-(∑ j, x j)/n)^2 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hs : (∑ i, (x i-(∑ j, x j)/n)^2) = (∑ i, (x i)^2)-(∑ i, x i)^2/n := by
    rw [finset_centered_expansion]
    simp only [card_univ, Fintype.card_fin]
    field_simp
    ring
  rw [uniform_permutation_loss, localFormula_b n hn, hs]

variable {V : Type*} [Fintype V] [DecidableEq V]

def hubMeanLoss (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (v : V) : ℝ :=
  (∑ p : Equiv.Perm {u // u ∈ G.neighborFinset v},
    (energy x-energy (actionState x ⟨v,p⟩))) /
      Fintype.card (Equiv.Perm {u // u ∈ G.neighborFinset v})

/- This reindexes actual neighbor permutations by permutations of finite indices. -/
theorem hubMeanLoss_permutation (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (v : V) :
    hubMeanLoss G x v =
      permutationLoss (Fintype.card {u // u ∈ G.neighborFinset v}) (x v)
        (fun i => x (((Fintype.equivFin {u // u ∈ G.neighborFinset v}).symm i).val)) := by
  let E := (Fintype.equivFin {u // u ∈ G.neighborFinset v}).symm
  have hp (p : Equiv.Perm {u // u ∈ G.neighborFinset v}) :
      energy x-energy (actionState x ⟨v,p⟩) =
      sweepLoss (x v) (List.ofFn (fun i => x ((p (E i)).val))) := by
    have hh : v ∉ actionOrder (G := G) ⟨v,p⟩ := by rw [actionOrder_mem]; exact G.loopless _
    have he := networkSweep_energy x v (actionOrder (G := G) ⟨v,p⟩) (actionOrder_nodup _) hh
    simpa [actionState, actionOrder, List.map_ofFn, E] using he
  unfold hubMeanLoss permutationLoss
  simp_rw [hp]
  have he := Equiv.sum_comp (Equiv.permCongr E)
    (fun p => sweepLoss (x v) (List.ofFn (fun i => x ((p (E i)).val))))
  rw [← he]
  simp [Equiv.permCongr_apply, Fintype.card_perm, E]

/- Lemma 1 for a physical graph hub, with no regularity assumption. -/
theorem hubMeanLoss_local_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) (v : V) (hd : 0 < G.degree v) :
    hubMeanLoss G x v = a (G.degree v)*localS G x v + b (G.degree v)*localH G x v := by
  let E := (Fintype.equivFin {u // u ∈ G.neighborFinset v}).symm
  have hc : Fintype.card {u // u ∈ G.neighborFinset v} = G.degree v := by
    simp only [Fintype.card_coe, G.card_neighborFinset_eq_degree]
  have hn : 0 < Fintype.card {u // u ∈ G.neighborFinset v} := by rw [hc]; exact hd
  have hs (z : V → ℝ) : (∑ i, z ((E i).val)) = ∑ u ∈ G.neighborFinset v, z u := by
    rw [Equiv.sum_comp E (fun u => z u.val), sum_coe_sort]
  rw [hubMeanLoss_permutation, uniform_permutation_SH _ hn]
  change a _*(∑ i, (x ((E i).val)-(∑ j, x ((E j).val))/_ )^2) + _ = _
  rw [hs x, hs (fun u => (x u-(∑ j ∈ G.neighborFinset v, x j)/
    (Fintype.card {u // u ∈ G.neighborFinset v} : ℝ))^2), hc]
  unfold localS localH neighborTotal
  ring

def uniformPolicy [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] : SweepPolicy G :=
  fun _ => uniformLaw (SweepAction G)

theorem action_count_regular (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) :
    Fintype.card (SweepAction G) = Fintype.card V*d.factorial := by
  simp only [SweepAction, Fintype.card_sigma, Fintype.card_perm, Fintype.card_coe, G.card_neighborFinset_eq_degree, hreg, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id]

/- Uniform actions mean uniform hubs and uniform orders on a regular graph. -/
theorem uniform_policy_loss [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    expected (uniformPolicy G x) (fun s => energy x-energy (actionState x s)) =
      (∑ v, hubMeanLoss G x v)/Fintype.card V := by
  have hN : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hc (v : V) : Fintype.card (Equiv.Perm {u // u ∈ G.neighborFinset v}) = d.factorial := by
    simp only [Fintype.card_perm, Fintype.card_coe, G.card_neighborFinset_eq_degree, hreg]
  unfold expected uniformPolicy uniformLaw hubMeanLoss
  simp only [action_count_regular G d hreg, Nat.cast_mul]
  rw [← mul_sum]
  change (1/(Fintype.card V*d.factorial : ℝ)) *
    (∑ s : (v : V) × Equiv.Perm {u // u ∈ G.neighborFinset v},
      (energy x-energy (actionState x s))) = _
  rw [Fintype.sum_sigma]
  simp_rw [hc]
  rw [← sum_div]
  ring

/- Proposition 2's actual expected-loss operator for uniform graph actions. -/
theorem uniform_graph_operator [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    expected (uniformPolicy G x) (fun s => energy x-energy (actionState x s)) =
      (2*a d*lapQuadratic G x-gamma d*energy (laplacian G x))/Fintype.card V := by
  rw [uniform_policy_loss G d hreg]
  have hh (v : V) : hubMeanLoss G x v = a d*localS G x v+b d*localH G x v := by
    have he := hubMeanLoss_local_identity G x v (by rw [hreg]; exact hd)
    simpa [hreg] using he
  simp_rw [hh]
  rw [graph_loss_polynomial G d hd hreg]

end
end HubAveraging
