import CutAndBudget
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option maxHeartbeats 3000000
namespace HubAveraging
noncomputable section
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def energy (x : V → ℝ) : ℝ := ∑ i, (x i)^2

def total (x : V → ℝ) : ℝ := ∑ i, x i

def disagreement (x : V → ℝ) : ℝ :=
  ∑ i, (x i - total x / Fintype.card V)^2

def pairUpdate (x : V → ℝ) (h l : V) : V → ℝ :=
  fun i => if i = h ∨ i = l then (x h+x l)/2 else x i

def networkSweep (x : V → ℝ) (h : V) : List V → (V → ℝ)
  | [] => x
  | l :: ls => networkSweep (pairUpdate x h l) h ls

omit [DecidableEq V] in
theorem disagreement_nonneg (x : V → ℝ) : 0 ≤ disagreement x := by
  unfold disagreement
  exact sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq V] in
theorem disagreement_of_total_zero (x : V → ℝ) (hx : total x = 0) :
    disagreement x = energy x := by simp [disagreement, hx, energy]

omit [Fintype V] in
theorem pairUpdate_off (x : V → ℝ) (h l i : V) (hi : i ≠ h) (hil : i ≠ l) :
    pairUpdate x h l i = x i := by simp [pairUpdate, hi, hil]

theorem pairUpdate_energy (x : V → ℝ) (h l : V) (hne : h ≠ l) :
    energy x - energy (pairUpdate x h l) = (x h-x l)^2/2 := by
  have he := supported_energy_loss ({h,l} : Finset V) x (pairUpdate x h l) (by
    intro i hi
    simp only [mem_insert, mem_singleton, not_or] at hi
    exact (pairUpdate_off x h l i hi.1 hi.2).symm)
  change energy x - energy (pairUpdate x h l) = _ at he
  rw [he]
  simp [sum_insert, hne, pairUpdate]
  ring

theorem pairUpdate_total (x : V → ℝ) (h l : V) (hne : h ≠ l) :
    total (pairUpdate x h l) = total x := by
  have he : (∑ i, (pairUpdate x h l i - x i)) =
      ∑ i ∈ ({h,l} : Finset V), (pairUpdate x h l i - x i) := by
    symm
    apply sum_subset (subset_univ _)
    intro i _ hi
    simp only [mem_insert, mem_singleton, not_or] at hi
    rw [pairUpdate_off x h l i hi.1 hi.2, sub_self]
  have hz : (∑ i ∈ ({h,l} : Finset V), (pairUpdate x h l i - x i)) = 0 := by
    simp [sum_insert, hne, pairUpdate]
  rw [hz, sum_sub_distrib] at he
  exact sub_eq_zero.mp he

theorem networkSweep_total (x : V → ℝ) (h : V) (ls : List V)
    (hh : h ∉ ls) : total (networkSweep x h ls) = total x := by
  induction ls generalizing x with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.mem_cons, not_or] at hh
    rw [networkSweep, ih _ hh.2, pairUpdate_total x h l hh.1]

/- A distinct-neighbor graph sweep is the physical list sweep, at the level
of its exact global energy loss. Previously visited vertices cannot reappear. -/
theorem networkSweep_energy (x : V → ℝ) (h : V) (ls : List V)
    (hn : ls.Nodup) (hh : h ∉ ls) :
    energy x - energy (networkSweep x h ls) = sweepLoss (x h) (ls.map x) := by
  induction ls generalizing x with
  | nil => simp [networkSweep, sweepLoss]
  | cons l ls ih =>
    simp only [List.nodup_cons] at hn
    simp only [List.mem_cons, not_or] at hh
    have hm : ls.map (pairUpdate x h l) = ls.map x := by
      apply List.map_congr_left
      intro i hi
      apply pairUpdate_off
      · exact fun he => hh.2 (he ▸ hi)
      · exact fun he => hn.1 (he ▸ hi)
    have he := ih (pairUpdate x h l) hn.2 hh.2
    rw [hm] at he
    have hhval : pairUpdate x h l h = (x h+x l)/2 := by simp [pairUpdate]
    rw [hhval] at he
    have hp := pairUpdate_energy x h l hh.1
    simp only [networkSweep, List.map_cons, sweepLoss]
    linarith

/- An action chooses a hub and a permutation of its actual neighbors. -/
def SweepAction (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (v : V) × Equiv.Perm {u // u ∈ G.neighborFinset v}

instance (G : SimpleGraph V) [DecidableRel G.Adj] : Fintype (SweepAction G) :=
  inferInstanceAs (Fintype ((v : V) × Equiv.Perm {u // u ∈ G.neighborFinset v}))

def actionOrder {G : SimpleGraph V} [DecidableRel G.Adj] (s : SweepAction G) : List V :=
  List.ofFn fun k => (s.2 ((Fintype.equivFin {u // u ∈ G.neighborFinset s.1}).symm k)).val

omit [DecidableEq V] in
theorem actionOrder_nodup {G : SimpleGraph V} [DecidableRel G.Adj] (s : SweepAction G) :
    (actionOrder s).Nodup := by
  apply List.nodup_ofFn.mpr
  exact Subtype.val_injective.comp (s.2.injective.comp (Fintype.equivFin _).symm.injective)

omit [DecidableEq V] in
theorem actionOrder_mem {G : SimpleGraph V} [DecidableRel G.Adj] (s : SweepAction G) (u : V) :
    u ∈ actionOrder s ↔ G.Adj s.1 u := by
  simp only [actionOrder, List.mem_ofFn]
  constructor
  · rintro ⟨k,hk⟩
    have hm := (s.2 ((Fintype.equivFin _).symm k)).property
    rw [hk] at hm
    exact (G.mem_neighborFinset _ _).mp hm
  · intro hu
    let z : {u // u ∈ G.neighborFinset s.1} := ⟨u, (G.mem_neighborFinset _ _).mpr hu⟩
    refine ⟨(Fintype.equivFin _) (s.2.symm z), ?_⟩
    simp [z]

omit [DecidableEq V] in
theorem actionOrder_length {G : SimpleGraph V} [DecidableRel G.Adj] (s : SweepAction G) :
    (actionOrder s).length = G.degree s.1 := by
  simp only [actionOrder, List.length_ofFn, Fintype.card_coe, G.card_neighborFinset_eq_degree]

/- A distribution on the finite set of physical hub/order outcomes. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ o, 0 ≤ weight o
  mass : ∑ o, weight o = 1

def expected {Ω : Type*} [Fintype Ω] (p : FiniteLaw Ω) (z : Ω → ℝ) : ℝ :=
  ∑ o, p.weight o * z o

def SweepPolicy (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (V → ℝ) → FiniteLaw (SweepAction G)

def actionState {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : V → ℝ) (s : SweepAction G) : V → ℝ := networkSweep x s.1 (actionOrder s)

def policyRatio {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : SweepPolicy G) (x : V → ℝ) : ℝ :=
  expected (P x) (fun s => disagreement (actionState x s)) / disagreement x

def worstResidual {G : SimpleGraph V} [DecidableRel G.Adj] (P : SweepPolicy G) : ℝ :=
  sSup {q | ∃ x : V → ℝ, 0 < disagreement x ∧ q = policyRatio P x}

def optimalResidual (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  sInf (Set.range (fun P : SweepPolicy G => worstResidual P))

/- Double counting neighboring values on a regular undirected graph. -/
omit [DecidableEq V] in
theorem regular_neighbor_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (z : V → ℝ) :
    (∑ v, ∑ u ∈ G.neighborFinset v, z u) = d * total z := by
  simp_rw [G.neighborFinset_eq_filter, sum_filter]
  rw [sum_comm]
  simp_rw [G.adj_comm]
  have hi (u : V) : (∑ v, if G.Adj u v then z u else 0) = d * z u := by
    rw [← sum_filter]
    simp [← G.neighborFinset_eq_filter, hreg]
  simp_rw [hi]
  exact (mul_sum univ _ _).symm

/- The opposite-sign witness has zero mean by regularity. -/
omit [DecidableEq V] in
theorem regular_bipartition_total_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (x : V → ℝ) (hopp : ∀ v u, G.Adj v u → x u = -x v) : total x = 0 := by
  have hsum (v : V) : (∑ u ∈ G.neighborFinset v, x u) = -(d * x v) := by
    calc
      _ = ∑ _u ∈ G.neighborFinset v, -x v := sum_congr rfl fun u hu => hopp v u ((G.mem_neighborFinset _ _).mp hu)
      _ = _ := by simp [hreg]
  have hs := regular_neighbor_sum G d hreg x
  simp_rw [hsum] at hs
  rw [sum_neg_distrib, ← mul_sum] at hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold total at *
  nlinarith

omit [DecidableEq V] in
theorem sign_energy (x : V → ℝ) (hs : ∀ v, x v = 1 ∨ x v = -1) :
    energy x = Fintype.card V := by
  have he (v : V) : (x v)^2 = 1 := by rcases hs v with h | h <;> norm_num [h]
  simp [energy, he]

/- The exact witness formula for physical updates of graph states. -/
theorem graph_witness_residual (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (x : V → ℝ) (hs : ∀ v, x v = 1 ∨ x v = -1)
    (hopp : ∀ v u, G.Adj v u → x u = -x v) (s : SweepAction G) :
    disagreement (actionState x s) = Fintype.card V - (8/3 : ℝ)*(1-r d) := by
  have hh : s.1 ∉ actionOrder s := by rw [actionOrder_mem]; exact G.loopless _
  have hzero := regular_bipartition_total_zero G d hd hreg x hopp
  have hpres := networkSweep_total x s.1 (actionOrder s) hh
  have hE := networkSweep_energy x s.1 (actionOrder s) (actionOrder_nodup s) hh
  have hL := all_opposite_orders_loss x s.1 (actionOrder s) d
    ((actionOrder_length s).trans (hreg s.1)) (hs s.1)
    (fun u hu => hopp s.1 u ((actionOrder_mem s u).mp hu))
  rw [hL, sign_energy x hs] at hE
  unfold actionState
  rw [disagreement_of_total_zero _ (hpres.trans hzero)]
  change energy (networkSweep x s.1 (actionOrder s)) = _
  linarith

omit [DecidableEq V] in
theorem centered_energy_expansion (x : V → ℝ) (m : ℝ) :
    (∑ i, (x i-m)^2) = energy x - 2*m*total x + Fintype.card V*m^2 := by
  calc
    _ = ∑ i, ((x i)^2 - 2*m*x i + m^2) := sum_congr rfl fun _ _ => by ring
    _ = _ := by simp [sum_add_distrib, sum_sub_distrib, ← mul_sum, energy, total]

omit [DecidableEq V] in
theorem disagreement_expansion [Nonempty V] (x : V → ℝ) :
    disagreement x = energy x - (total x)^2 / Fintype.card V := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [disagreement, centered_energy_expansion]
  field_simp
  ring

omit [DecidableEq V] in
theorem disagreement_loss [Nonempty V] (x y : V → ℝ) (ht : total y = total x) :
    disagreement x - disagreement y = energy x - energy y := by
  rw [disagreement_expansion, disagreement_expansion, ht]
  ring

theorem sweepLoss_nonneg (h : ℝ) (ls : List ℝ) : 0 ≤ sweepLoss h ls := by
  induction ls generalizing h with
  | nil => simp [sweepLoss]
  | cons l ls ih =>
    exact add_nonneg (div_nonneg (sq_nonneg _) (by norm_num)) (ih _)

theorem action_disagreement_le [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (x : V → ℝ) (s : SweepAction G) : disagreement (actionState x s) ≤ disagreement x := by
  have hh : s.1 ∉ actionOrder s := by rw [actionOrder_mem]; exact G.loopless _
  have he := networkSweep_energy x s.1 (actionOrder s) (actionOrder_nodup s) hh
  have ht := networkSweep_total x s.1 (actionOrder s) hh
  have hl := disagreement_loss x (actionState x s) ht
  have hn := sweepLoss_nonneg (x s.1) ((actionOrder s).map x)
  change energy x - energy (actionState x s) = _ at he
  linarith

theorem policyRatio_le_one [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : SweepPolicy G) (x : V → ℝ) (hx : 0 < disagreement x) : policyRatio P x ≤ 1 := by
  apply (div_le_iff₀ hx).2
  calc
    _ ≤ ∑ s, (P x).weight s * disagreement x := by
      apply sum_le_sum
      intro s _
      exact mul_le_mul_of_nonneg_left (action_disagreement_le x s) ((P x).nonneg s)
    _ = _ := by rw [← sum_mul, (P x).mass]

theorem ratio_le_worstResidual [Nonempty V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (P : SweepPolicy G) (x : V → ℝ) (hx : 0 < disagreement x) :
    policyRatio P x ≤ worstResidual P := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro q ⟨y,hy,rfl⟩
    exact policyRatio_le_one P y hy
  · exact ⟨x,hx,rfl⟩

theorem policy_witness_exact [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (x : V → ℝ) (hs : ∀ v, x v = 1 ∨ x v = -1)
    (hopp : ∀ v u, G.Adj v u → x u = -x v) (P : SweepPolicy G) :
    policyRatio P x = 1 - (8/3 : ℝ)*(1-r d)/Fintype.card V := by
  have hx : disagreement x = Fintype.card V := by
    rw [disagreement_of_total_zero _ (regular_bipartition_total_zero G d hd hreg x hopp), sign_energy x hs]
  unfold policyRatio expected
  rw [hx]
  apply policy_witness_ratio _ _ _ _ (by exact_mod_cast Fintype.card_pos) (P x).mass
  exact graph_witness_residual G d hd hreg x hs hopp

def signState (color : V → Bool) : V → ℝ := fun v => if color v then 1 else -1

omit [Fintype V] [DecidableEq V] in
theorem signState_values (color : V → Bool) (v : V) :
    signState color v = 1 ∨ signState color v = -1 := by
  cases h : color v <;> simp [signState, h]

omit [Fintype V] [DecidableEq V] in
theorem signState_opposite (color : V → Bool) (v u : V) (h : color v ≠ color u) :
    signState color u = -signState color v := by
  cases hv : color v <;> cases hu : color u <;> simp_all [signState]

/- Theorem 3, universal lower-bound part: a genuine graph policy and its
supremum over all input states, with bipartiteness given by a proper coloring. -/
theorem bipartite_policy_lower_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u)
    (P : SweepPolicy G) :
    1 - (8/3 : ℝ)*(1-r d)/Fintype.card V ≤ worstResidual P := by
  have hopp := fun v u (h : G.Adj v u) => signState_opposite color v u (hc v u h)
  have hx : disagreement (signState color) = Fintype.card V := by
    rw [disagreement_of_total_zero _ (regular_bipartition_total_zero G d hd hreg _ hopp),
      sign_energy _ (signState_values color)]
  rw [← policy_witness_exact G d hd hreg _ (signState_values color) hopp P]
  apply ratio_le_worstResidual
  rw [hx]
  exact_mod_cast Fintype.card_pos

def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  weight := fun _ => 1 / Fintype.card Ω
  nonneg := fun _ => by positivity
  mass := by simp [Fintype.card_ne_zero]

instance [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] : Nonempty (SweepAction G) :=
  ⟨⟨Classical.arbitrary V, Equiv.refl _⟩⟩

/- Taking the infimum over all state-dependent randomized policies preserves
the obstruction. The policy class is proved nonempty by its uniform policy. -/
theorem bipartite_minimax_lower_bound [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d)
    (color : V → Bool) (hc : ∀ v u, G.Adj v u → color v ≠ color u) :
    1 - (8/3 : ℝ)*(1-r d)/Fintype.card V ≤ optimalResidual G := by
  apply le_csInf
  · exact ⟨worstResidual (fun _ => uniformLaw (SweepAction G)),
      ⟨fun _ => uniformLaw (SweepAction G), rfl⟩⟩
  · rintro q ⟨P,rfl⟩
    exact bipartite_policy_lower_bound G d hd hreg color hc P

end
end HubAveraging
