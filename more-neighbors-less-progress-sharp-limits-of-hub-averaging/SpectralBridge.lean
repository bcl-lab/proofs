import Network
import Mathlib.LinearAlgebra.Matrix.Spectrum

set_option maxHeartbeats 4000000
namespace HubAveraging
noncomputable section
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem energy_dot (x : V → ℝ) : energy x = x ⬝ᵥ x := by
  simp [energy, dotProduct, pow_two]

theorem orthogonal_dot (U : Matrix V V ℝ) (hU : Uᵀ*U = 1) (x y : V → ℝ) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ y) = x ⬝ᵥ y := by
  rw [dotProduct_mulVec, vecMul_mulVec, hU, vecMul_one]

/-- Construct the spectral energy expansion from Mathlib's proved spectral
theorem. The coordinates and eigenvalues are those of the actual matrix. -/
theorem hermitian_polynomial_expansion (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (x : V → ℝ) (a g : ℝ) :
    let z := (star (hA.eigenvectorUnitary : Matrix V V ℝ)) *ᵥ x
    energy x = energy z ∧
    2*a*(x ⬝ᵥ (A *ᵥ x)) - g*energy (A *ᵥ x) =
      ∑ i, (z i)^2*(2*a*hA.eigenvalues i-g*(hA.eigenvalues i)^2) := by
  let U : Matrix V V ℝ := hA.eigenvectorUnitary
  let z := (star U) *ᵥ x
  have hUt : Uᵀ = star U := by simp [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hU : Uᵀ*U = 1 := by
    rw [hUt]
    exact unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUU : U*star U = 1 := unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hx : U *ᵥ z = x := by
    dsimp only [z]
    rw [mulVec_mulVec, hUU, one_mulVec]
  have hAx : A *ᵥ x = U *ᵥ ((diagonal hA.eigenvalues) *ᵥ z) := by
    calc
      _ = ((hA.eigenvectorUnitary : Matrix V V ℝ) * diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
          star (hA.eigenvectorUnitary : Matrix V V ℝ)) *ᵥ x := congrArg (fun B : Matrix V V ℝ => B *ᵥ x) hA.spectral_theorem
      _ = _ := by rw [← mulVec_mulVec, ← mulVec_mulVec]; rfl
  have hE : energy x = energy z := by
    rw [energy_dot, ← hx, orthogonal_dot U hU, ← energy_dot]
  have hQ : x ⬝ᵥ (A *ᵥ x) = ∑ i, hA.eigenvalues i*(z i)^2 := by
    rw [hAx, ← hx, orthogonal_dot U hU]
    unfold dotProduct
    apply sum_congr rfl
    intro i _
    rw [mulVec_diagonal]
    ring
  have hR : energy (A *ᵥ x) = ∑ i, (hA.eigenvalues i)^2*(z i)^2 := by
    rw [hAx, energy_dot, orthogonal_dot U hU, ← energy_dot]
    unfold energy
    apply sum_congr rfl
    intro i _
    rw [mulVec_diagonal]
    ring
  change energy x = energy z ∧ _
  refine ⟨hE, ?_⟩
  rw [hQ,hR,mul_sum,mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  ring

/-- A genuine matrix spectral bound. The zero-eigenvalue coordinates must
vanish; graph applications discharge this by centering and connectivity. -/
theorem hermitian_threshold_bound (A : Matrix V V ℝ) (hA : A.IsHermitian)
    (d : ℕ) (hd : 2 ≤ d) (x : V → ℝ)
    (hzero : ∀ i, hA.eigenvalues i = 0 →
      ((star (hA.eigenvectorUnitary : Matrix V V ℝ)) *ᵥ x) i = 0)
    (hl : ∀ i, hA.eigenvalues i ≠ 0 → tau d ≤ hA.eigenvalues i)
    (hu : ∀ i, hA.eigenvalues i ≤ 2*d) :
    (8/3 : ℝ)*(1-r d)*energy x ≤
      2*a d*(x ⬝ᵥ (A *ᵥ x)) - gamma d*energy (A *ᵥ x) := by
  obtain ⟨hE,hF⟩ := hermitian_polynomial_expansion A hA x (a d) (gamma d)
  rw [hF,hE]
  unfold energy
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  by_cases hz : hA.eigenvalues i = 0
  · rw [hzero i hz]
    simp
  · have hi := mul_le_mul_of_nonneg_left (spectral_threshold d hd (hA.eigenvalues i)
      (hl i hz) (hu i)) (sq_nonneg (((star (hA.eigenvectorUnitary : Matrix V V ℝ)) *ᵥ x) i))
    simpa [f, mul_comm] using hi

end
end HubAveraging
