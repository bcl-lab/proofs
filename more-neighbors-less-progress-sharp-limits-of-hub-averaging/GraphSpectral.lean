import SpectralBridge
import EdgeProcess
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

set_option maxHeartbeats 4000000
namespace HubAveraging
noncomputable section
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem laplacian_matrix (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → ℝ) :
    (G.lapMatrix ℝ) *ᵥ x = laplacian G x := by
  ext v
  simp [G.lapMatrix_mulVec_apply, laplacian, neighborTotal]

omit [DecidableEq V] in
theorem lapQuadratic_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (x : V → ℝ) :
    lapQuadratic G x ≤ 2*d*energy x := by
  have he := directed_difference_sum G d hreg x
  have hb : (∑ v, ∑ u ∈ G.neighborFinset v, (x v-x u)^2) ≤
      ∑ v, ∑ u ∈ G.neighborFinset v, (2*(x v)^2+2*(x u)^2) := by
    apply sum_le_sum
    intro v _
    apply sum_le_sum
    intro u _
    nlinarith [sq_nonneg (x v+x u)]
  simp_rw [sum_add_distrib, sum_const, nsmul_eq_mul, G.card_neighborFinset_eq_degree, hreg] at hb
  rw [regular_neighbor_sum G d hreg] at hb
  have h1 : (∑ v, (d : ℝ)*(2*(x v)^2)) = 2*d*energy x := by
    unfold energy
    rw [mul_sum]
    apply sum_congr rfl
    intro v _
    ring
  have h2 : total (fun u => 2*(x u)^2) = 2*energy x := by
    unfold total energy
    rw [mul_sum]
  rw [h1,h2,he] at hb
  nlinarith

def lapHermitian (G : SimpleGraph V) [DecidableRel G.Adj] : (G.lapMatrix ℝ).IsHermitian :=
  (G.posSemidef_lapMatrix ℝ).1

theorem lap_eigenvalue_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (i : V) :
    (lapHermitian G).eigenvalues i ≤ 2*d := by
  let ev : V → ℝ := (lapHermitian G).eigenvectorBasis i
  have hnorm : energy ev = 1 := by
    have hh := congrArg (fun t : ℝ => t^2) ((lapHermitian G).eigenvectorBasis.orthonormal.1 i)
    dsimp only at hh
    rw [PiLp.norm_sq_eq_of_L2] at hh
    simpa only [Real.norm_eq_abs, sq_abs, energy, ev, one_pow] using hh
  have he : (lapHermitian G).eigenvalues i = lapQuadratic G ev := by
    have hh := (lapHermitian G).eigenvalues_eq i
    simpa [lapQuadratic, ← laplacian_matrix, dotProduct, ev, star_trivial] using hh
  have hb := lapQuadratic_upper G d hreg ev
  rw [hnorm, mul_one] at hb
  rw [he]
  exact hb

theorem centered_zero_eigen_coordinates (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (x : V → ℝ) (hx : total x = 0)
    (i : V) (hi : (lapHermitian G).eigenvalues i = 0) :
    ((star ((lapHermitian G).eigenvectorUnitary : Matrix V V ℝ)) *ᵥ x) i = 0 := by
  letI := hconn.nonempty
  let ev : V → ℝ := (lapHermitian G).eigenvectorBasis i
  have he : (G.lapMatrix ℝ) *ᵥ ev = 0 := by
    have hh := (lapHermitian G).mulVec_eigenvectorBasis i
    simpa [hi, ev] using hh
  have hr := (G.lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable ev).mp he
  let v0 : V := Classical.arbitrary V
  have hv (v : V) : ev v = ev v0 := hr v v0 (hconn v v0)
  change (∑ v, (star ((lapHermitian G).eigenvectorUnitary : Matrix V V ℝ)) i v * x v) = 0
  simp only [star_eq_conjTranspose, conjTranspose_apply, star_trivial,
    Matrix.IsHermitian.eigenvectorUnitary_apply]
  change (∑ v, ev v*x v) = 0
  simp_rw [hv]
  rw [← mul_sum]
  change ev v0 * total x = 0
  rw [hx, mul_zero]

/-- The manuscript's spectral condition stated on the nonzero Laplacian
eigenvalues. For a connected graph this is the condition on its spectral gap. -/
def spectralGapAtLeast (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) : Prop :=
  ∀ i, (lapHermitian G).eigenvalues i ≠ 0 → t ≤ (lapHermitian G).eigenvalues i

/-- The graph spectral bridge, with the zero mode and upper spectral bound
proved from connectivity and regularity. -/
theorem centered_graph_threshold (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 2 ≤ d) (hreg : ∀ v, G.degree v = d)
    (hgap : spectralGapAtLeast G (tau d)) (x : V → ℝ) (hx : total x = 0) :
    (8/3 : ℝ)*(1-r d)*disagreement x ≤
      2*a d*lapQuadratic G x-gamma d*energy (laplacian G x) := by
  have hb := hermitian_threshold_bound (G.lapMatrix ℝ) (lapHermitian G) d hd x
    (centered_zero_eigen_coordinates G hconn x hx) hgap (lap_eigenvalue_upper G d hreg)
  rw [laplacian_matrix, ← disagreement_of_total_zero x hx] at hb
  exact hb

end
end HubAveraging
