import Minimax
import Mathlib.Data.Finset.Max

set_option maxHeartbeats 4000000
namespace HubAveraging
noncomputable section
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [Nonempty V] in
theorem lap_eigenvector_energy (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    energy (fun v => (lapHermitian G).eigenvectorBasis i v) = 1 := by
  have hh := congrArg (fun t : ℝ => t^2) ((lapHermitian G).eigenvectorBasis.orthonormal.1 i)
  dsimp only at hh
  rw [PiLp.norm_sq_eq_of_L2] at hh
  simpa only [Real.norm_eq_abs, sq_abs, energy, one_pow] using hh

omit [Nonempty V] in
theorem lap_eigenvector_centered (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hreg : ∀ v, G.degree v = d) (i : V)
    (hi : (lapHermitian G).eigenvalues i ≠ 0) :
    total (fun v => (lapHermitian G).eigenvectorBasis i v) = 0 := by
  have he := (lapHermitian G).mulVec_eigenvectorBasis i
  rw [laplacian_matrix] at he
  have ht := congrArg total he
  rw [laplacian_total G d hreg] at ht
  simp only [total, Pi.smul_apply, smul_eq_mul, ← mul_sum] at ht
  exact (mul_eq_zero.mp ht.symm).resolve_left hi

omit [Nonempty V] in
theorem lap_eigenvector_moments (G : SimpleGraph V) [DecidableRel G.Adj] (i : V) :
    let ev : V → ℝ := (lapHermitian G).eigenvectorBasis i
    lapQuadratic G ev = (lapHermitian G).eigenvalues i ∧
    energy (laplacian G ev) = ((lapHermitian G).eigenvalues i)^2 := by
  let ev : V → ℝ := (lapHermitian G).eigenvectorBasis i
  have hn := lap_eigenvector_energy G i
  have he := (lapHermitian G).mulVec_eigenvectorBasis i
  rw [laplacian_matrix] at he
  have hp (v : V) : laplacian G ev v = (lapHermitian G).eigenvalues i*ev v := congrFun he v
  constructor
  · change (∑ v, ev v*laplacian G ev v) = _
    calc
      _ = (lapHermitian G).eigenvalues i*energy ev := by
        unfold energy
        rw [mul_sum]
        apply sum_congr rfl
        intro v _
        rw [hp]
        ring
      _ = _ := by rw [hn,mul_one]
  · change (∑ v, (laplacian G ev v)^2) = _
    simp_rw [hp,mul_pow]
    rw [← mul_sum]
    change ((lapHermitian G).eigenvalues i)^2*energy ev = _
    rw [hn,mul_one]

theorem uniform_eigenvector_ratio (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) (i : V)
    (hi : (lapHermitian G).eigenvalues i ≠ 0) :
    policyRatio (uniformPolicy G) (fun v => (lapHermitian G).eigenvectorBasis i v) =
      1-f d ((lapHermitian G).eigenvalues i)/Fintype.card V := by
  have hv : disagreement (fun v => (lapHermitian G).eigenvectorBasis i v) = 1 := by
    rw [disagreement_of_total_zero _ (lap_eigenvector_centered G d hreg i hi), lap_eigenvector_energy]
  obtain ⟨hQ,hR⟩ := lap_eigenvector_moments G i
  unfold policyRatio
  rw [uniform_expected_residual G d hd hreg, hv, hQ, hR, div_one]
  rfl

theorem graph_interval_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 2 ≤ d) (hreg : ∀ v, G.degree v = d)
    (l u : ℝ)
    (hl : ∀ i, (lapHermitian G).eigenvalues i ≠ 0 → l ≤ (lapHermitian G).eigenvalues i)
    (hu : ∀ i, (lapHermitian G).eigenvalues i ≠ 0 → (lapHermitian G).eigenvalues i ≤ u)
    (x : V → ℝ) :
    min (f d l) (f d u)*disagreement x ≤
      2*a d*lapQuadratic G x-gamma d*energy (laplacian G x) := by
  let y := centeredState x
  obtain ⟨hE,hF⟩ := hermitian_polynomial_expansion (G.lapMatrix ℝ) (lapHermitian G) y (a d) (gamma d)
  have hb : min (f d l) (f d u)*energy y ≤
      2*a d*(y ⬝ᵥ ((G.lapMatrix ℝ) *ᵥ y))-gamma d*energy ((G.lapMatrix ℝ) *ᵥ y) := by
    rw [hE,hF]
    unfold energy
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    by_cases hz : (lapHermitian G).eigenvalues i = 0
    · rw [centered_zero_eigen_coordinates G hconn y (centeredState_total x) i hz]
      simp
    · have hh := concave_quadratic_endpoint (a d) (gamma d) l u ((lapHermitian G).eigenvalues i)
        (gamma_pos d hd).le (hl i hz) (hu i hz)
      have hp := mul_le_mul_of_nonneg_left hh
        (sq_nonneg (((star ((lapHermitian G).eigenvectorUnitary : Matrix V V ℝ)) *ᵥ y) i))
      simpa [f,mul_comm] using hp
  rw [laplacian_matrix] at hb
  change min (f d l) (f d u)*energy (centeredState x) ≤
    2*a d*lapQuadratic G (centeredState x)-gamma d*energy (laplacian G (centeredState x)) at hb
  rw [centeredState_energy, lapQuadratic_centeredState G d hreg, laplacian_centeredState] at hb
  exact hb

/- Proposition 2's exact endpoint formula. The indices are specified as the
smallest and largest nonzero eigenvalues of the actual Laplacian. -/
theorem uniform_endpoint_formula (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 2 ≤ d) (hreg : ∀ v, G.degree v = d)
    (lo hi : V) (hlo0 : (lapHermitian G).eigenvalues lo ≠ 0)
    (hhi0 : (lapHermitian G).eigenvalues hi ≠ 0)
    (hl : ∀ i, (lapHermitian G).eigenvalues i ≠ 0 →
      (lapHermitian G).eigenvalues lo ≤ (lapHermitian G).eigenvalues i)
    (hu : ∀ i, (lapHermitian G).eigenvalues i ≠ 0 →
      (lapHermitian G).eigenvalues i ≤ (lapHermitian G).eigenvalues hi) :
    1-worstResidual (uniformPolicy G) =
      min (f d ((lapHermitian G).eigenvalues lo)) (f d ((lapHermitian G).eigenvalues hi))/Fintype.card V := by
  let C := min (f d ((lapHermitian G).eigenvalues lo)) (f d ((lapHermitian G).eigenvalues hi))
  have hN : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hev (i : V) (hz : (lapHermitian G).eigenvalues i ≠ 0) :
      0 < disagreement (fun v => (lapHermitian G).eigenvectorBasis i v) := by
    rw [disagreement_of_total_zero _ (lap_eigenvector_centered G d hreg i hz), lap_eigenvector_energy]
    norm_num
  have hU : worstResidual (uniformPolicy G) ≤ 1-C/Fintype.card V := by
    apply csSup_le
    · exact ⟨_, ⟨(fun v => (lapHermitian G).eigenvectorBasis lo v), hev lo hlo0, rfl⟩⟩
    · rintro q ⟨x,hx,rfl⟩
      unfold policyRatio
      rw [uniform_expected_residual G d (by omega) hreg]
      apply (div_le_iff₀ hx).2
      have hb := div_le_div_of_nonneg_right (graph_interval_bound G hconn d hd hreg _ _ hl hu x) hN.le
      calc
        _ ≤ disagreement x-C*disagreement x/Fintype.card V := sub_le_sub_left hb _
        _ = _ := by ring
  have hL (i : V) (hz : (lapHermitian G).eigenvalues i ≠ 0) :
      1-f d ((lapHermitian G).eigenvalues i)/Fintype.card V ≤ worstResidual (uniformPolicy G) := by
    rw [← uniform_eigenvector_ratio G d (by omega) hreg i hz]
    exact ratio_le_worstResidual _ _ (hev i hz)
  have hC : 1-C/Fintype.card V ≤ worstResidual (uniformPolicy G) := by
    rcases le_total (f d ((lapHermitian G).eigenvalues lo)) (f d ((lapHermitian G).eigenvalues hi)) with h | h
    · simpa only [C,min_eq_left h] using hL lo hlo0
    · simpa only [C,min_eq_right h] using hL hi hhi0
  change 1-worstResidual (uniformPolicy G) = C/Fintype.card V
  linarith

/- A positive regular degree guarantees a nonzero graph eigenvalue. -/
theorem exists_nonzero_lap_eigenvalue (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : ∀ v, G.degree v = d) :
    ∃ i, (lapHermitian G).eigenvalues i ≠ 0 := by
  classical
  have hA : G.lapMatrix ℝ ≠ 0 := by
    intro hz
    let v : V := Classical.arbitrary V
    have hh := congrArg (fun M : Matrix V V ℝ => M v v) hz
    dsimp only at hh
    have hdiag : (G.lapMatrix ℝ) v v = d := by
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix, hreg]
    rw [hdiag] at hh
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    change (d : ℝ) = 0 at hh
    linarith
  by_contra! hz
  have heigs : (lapHermitian G).eigenvalues = (fun _ => (0 : ℝ)) := funext hz
  have he := (lapHermitian G).spectral_theorem
  apply hA
  simpa [heigs] using he

/- All endpoint indices needed for Proposition 2 exist, and its exact formula
holds for these extremal nonzero graph eigenvalues. -/
theorem exists_uniform_spectral_endpoints (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (d : ℕ) (hd : 2 ≤ d) (hreg : ∀ v, G.degree v = d) :
    ∃ lo hi : V, (lapHermitian G).eigenvalues lo ≠ 0 ∧ (lapHermitian G).eigenvalues hi ≠ 0 ∧
      (∀ i, (lapHermitian G).eigenvalues i ≠ 0 →
        (lapHermitian G).eigenvalues lo ≤ (lapHermitian G).eigenvalues i) ∧
      (∀ i, (lapHermitian G).eigenvalues i ≠ 0 →
        (lapHermitian G).eigenvalues i ≤ (lapHermitian G).eigenvalues hi) ∧
      1-worstResidual (uniformPolicy G) =
        min (f d ((lapHermitian G).eigenvalues lo)) (f d ((lapHermitian G).eigenvalues hi))/Fintype.card V := by
  classical
  let s := univ.filter (fun i => (lapHermitian G).eigenvalues i ≠ 0)
  obtain ⟨i,hi⟩ := exists_nonzero_lap_eigenvalue G d (by omega) hreg
  have hs : s.Nonempty := ⟨i, mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  obtain ⟨lo,hlo,hmin⟩ := exists_min_image s (lapHermitian G).eigenvalues hs
  obtain ⟨hi,hhi,hmax⟩ := exists_max_image s (lapHermitian G).eigenvalues hs
  have hlo0 := (mem_filter.mp hlo).2
  have hhi0 := (mem_filter.mp hhi).2
  have hL := fun j hj => hmin j (mem_filter.mpr ⟨mem_univ _,hj⟩)
  have hU := fun j hj => hmax j (mem_filter.mpr ⟨mem_univ _,hj⟩)
  exact ⟨lo,hi,hlo0,hhi0,hL,hU,uniform_endpoint_formula G hconn d hd hreg lo hi hlo0 hhi0 hL hU⟩

end
end HubAveraging
