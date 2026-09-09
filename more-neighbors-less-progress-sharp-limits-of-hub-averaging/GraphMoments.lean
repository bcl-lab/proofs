import Network
import Mathlib.Algebra.BigOperators.Field

set_option maxHeartbeats 3000000
namespace HubAveraging
noncomputable section
open Finset
variable {V : Type*} [Fintype V]

def neighborTotal (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (v : V) : ℝ :=
  ∑ u ∈ G.neighborFinset v, x u

def laplacian (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (v : V) : ℝ :=
  G.degree v * x v - neighborTotal G x v

def lapQuadratic (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) : ℝ :=
  ∑ v, x v * laplacian G x v

def localS (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (v : V) : ℝ :=
  ∑ u ∈ G.neighborFinset v, (x u - neighborTotal G x v / G.degree v)^2

def localH (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) (v : V) : ℝ :=
  (G.degree v : ℝ) / (G.degree v + 1) * (x v-neighborTotal G x v/G.degree v)^2

omit [Fintype V] in
theorem finset_centered_expansion (s : Finset V) (x : V → ℝ) (m : ℝ) :
    (∑ i ∈ s, (x i-m)^2) = (∑ i ∈ s, (x i)^2) - 2*m*(∑ i ∈ s, x i) + s.card*m^2 := by
  calc
    _ = ∑ i ∈ s, ((x i)^2 - 2*m*x i + m^2) := sum_congr rfl fun _ _ => by ring
    _ = _ := by simp [sum_add_distrib, sum_sub_distrib, ← mul_sum]

theorem localS_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) (v : V) :
    localS G x v = (∑ u ∈ G.neighborFinset v, (x u)^2) - (neighborTotal G x v)^2/d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  rw [localS, hreg, finset_centered_expansion, G.card_neighborFinset_eq_degree, hreg]
  change _ - 2 * (neighborTotal G x v / d) * neighborTotal G x v + _ = _
  field_simp
  ring

theorem localH_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) (v : V) :
    localH G x v = (laplacian G x v)^2/(d*(d+1)) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hd1 : (d : ℝ)+1 ≠ 0 := by positivity
  unfold localH laplacian
  rw [hreg]
  field_simp
  ring

theorem lapQuadratic_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    lapQuadratic G x = d * energy x - ∑ v, x v * neighborTotal G x v := by
  unfold lapQuadratic laplacian energy
  simp_rw [hreg]
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro v _
  ring

theorem lap_energy_expansion (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    energy (laplacian G x) = (d : ℝ)^2 * energy x -
      2*d*(∑ v, x v * neighborTotal G x v) + energy (neighborTotal G x) := by
  unfold energy laplacian
  simp_rw [hreg]
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  ring

/- Equation (8), first identity, derived from graph adjacency and regularity. -/
theorem graph_S_moment (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    (∑ v, localS G x v) = 2*lapQuadratic G x - energy (laplacian G x)/d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  simp_rw [localS_expansion G d hd hreg]
  rw [sum_sub_distrib, regular_neighbor_sum G d hreg, ← sum_div,
    lapQuadratic_expansion G d hreg, lap_energy_expansion G d hreg]
  change d * energy x - energy (neighborTotal G x) / d = _
  field_simp
  ring

/- Equation (8), second identity, for the actual graph Laplacian. -/
theorem graph_H_moment (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    (∑ v, localH G x v) = energy (laplacian G x)/(d*(d+1)) := by
  simp_rw [localH_expansion G d hd hreg]
  rw [← sum_div]
  rfl

/- Aggregation of the two physical neighborhood energies is exactly the
paper's Laplacian polynomial; no moment identities are assumed. -/
theorem graph_loss_polynomial (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    (∑ v, (a d*localS G x v + b d*localH G x v)) =
      2*a d*lapQuadratic G x - gamma d*energy (laplacian G x) := by
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  exact loss_polynomial_from_moments d hd _ _ _ _
    (graph_S_moment G d hd hreg x) (graph_H_moment G d hd hreg x)

end
end HubAveraging
