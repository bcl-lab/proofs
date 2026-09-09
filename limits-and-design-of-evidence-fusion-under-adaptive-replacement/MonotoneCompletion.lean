import Cardinality
import Completion

open scoped BigOperators NNReal
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def eraseCoordinates (C : Finset ι) (x : ι → ℝ≥0) : ι → ℝ≥0 :=
  fun i => if i ∈ C then 0 else x i

def trimCompletion (k : ℕ) (f : (ι → ℝ≥0) → ℝ) (x : ι → ℝ≥0) : ℝ :=
  (cardinalityAttacks k).inf' (cardinalityAttacks_nonempty k)
    (fun C => f (eraseCoordinates C x))

theorem erase_hamming_le (C : Finset ι) (x : ι → ℝ≥0) :
    hamming x (eraseCoordinates C x) ≤ C.card := by
  apply Finset.card_le_card
  intro i hi
  by_contra hn
  simpa [differences,eraseCoordinates,hn] using hi

theorem trimCompletion_le (k : ℕ) (f : (ι → ℝ≥0) → ℝ) (hf : Monotone f)
    (x y : ι → ℝ≥0) (hxy : hamming x y ≤ k) : trimCompletion k f x ≤ f y := by
  have hC : differences x y ∈ cardinalityAttacks k :=
    (mem_cardinalityAttacks k _).mpr hxy
  apply (Finset.inf'_le _ hC).trans
  apply hf
  intro i
  by_cases hi : i ∈ differences x y
  · simp [eraseCoordinates,hi]
  · have he : x i = y i := by simpa [differences] using hi
    simp [eraseCoordinates,hi,he]

theorem trimCompletion_attained (k : ℕ) (f : (ι → ℝ≥0) → ℝ) (x : ι → ℝ≥0) :
    ∃ y, hamming x y ≤ k ∧ trimCompletion k f x = f y := by
  obtain ⟨C,hC,he⟩ := Finset.exists_mem_eq_inf' (cardinalityAttacks_nonempty k)
    (fun C => f (eraseCoordinates C x))
  exact ⟨eraseCoordinates C x,(erase_hamming_le C x).trans
    ((mem_cardinalityAttacks k C).mp hC),he⟩

theorem trimCompletion_isLeast (k : ℕ) (f : (ι → ℝ≥0) → ℝ) (hf : Monotone f)
    (x : ι → ℝ≥0) :
    IsLeast {v | ∃ y, hamming x y ≤ k ∧ v = f y} (trimCompletion k f x) := by
  refine ⟨trimCompletion_attained k f x,?_⟩
  rintro v ⟨y,hy,rfl⟩
  exact trimCompletion_le k f hf x y hy

theorem monotone_trimCompletion (k : ℕ) (f : (ι → ℝ≥0) → ℝ) (hf : Monotone f) :
    Monotone (trimCompletion k f) := by
  intro x y hxy
  obtain ⟨C,hC,he⟩ := Finset.exists_mem_eq_inf' (cardinalityAttacks_nonempty k)
    (fun C => f (eraseCoordinates C y))
  change trimCompletion k f x ≤ (cardinalityAttacks k).inf'
    (cardinalityAttacks_nonempty k) (fun C => f (eraseCoordinates C y))
  rw [he]
  apply (Finset.inf'_le _ hC).trans
  apply hf
  intro i
  by_cases hi : i ∈ C <;> simp [eraseCoordinates,hi,hxy i]

theorem trimCompletion_composition (k l : ℕ) (f : (ι → ℝ≥0) → ℝ) (hf : Monotone f)
    (x : ι → ℝ≥0) :
    trimCompletion l (trimCompletion k f) x =
      trimCompletion (min (Fintype.card ι) (k+l)) f x := by
  apply le_antisymm
  · obtain ⟨z,hxz,hz⟩ := trimCompletion_attained (min (Fintype.card ι) (k+l)) f x
    have hxz' : hamming x z ≤ min (Fintype.card ι) (l+k) := by simpa [Nat.add_comm] using hxz
    obtain ⟨y,hxy,hyz⟩ := (hamming_ball_composition x z l k).mpr hxz'
    rw [hz]
    exact (trimCompletion_le l _ (monotone_trimCompletion k f hf) x y hxy).trans
      (trimCompletion_le k f hf y z hyz)
  · obtain ⟨y,hxy,hy⟩ := trimCompletion_attained l (trimCompletion k f) x
    obtain ⟨z,hyz,hz⟩ := trimCompletion_attained k f y
    rw [hy,hz]
    apply trimCompletion_le _ f hf x z
    have hh := (hamming_ball_composition x z l k).mp ⟨y,hxy,hyz⟩
    simpa [Nat.add_comm] using hh

theorem monotone_affineProduct (b lam : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hl : ∀ i, 0 ≤ lam i) :
    Monotone (fun x : ι → ℝ≥0 => ∏ i, (b i+lam i*(x i : ℝ))) := by
  intro x y hxy
  apply Finset.prod_le_prod
  · intro i _; exact add_nonneg (hb i) (mul_nonneg (hl i) (x i).coe_nonneg)
  · intro i _
    exact add_le_add_left (mul_le_mul_of_nonneg_left
      (show (x i : ℝ) ≤ (y i : ℝ) from hxy i) (hl i)) _

theorem product_completion (k : ℕ) (b lam : ι → ℝ) (x : ι → ℝ≥0) :
    trimCompletion k (fun z : ι → ℝ≥0 => ∏ i, (b i+lam i*(z i : ℝ))) x =
      robustProduct b lam (fun i => (x i : ℝ)) (cardinalityAttacks k)
        (cardinalityAttacks_nonempty k) := by
  unfold trimCompletion robustProduct
  congr 1
  funext C
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ C <;> simp [eraseCoordinates,hi]

/-- Exact worst replacement value of the corrected product. -/
theorem robustProduct_worst_replacement (k l : ℕ) (b lam : ι → ℝ)
    (hb : ∀ i, 0 ≤ b i) (hl : ∀ i, 0 ≤ lam i) (x : ι → ℝ≥0) :
    IsLeast {v | ∃ y : ι → ℝ≥0, hamming x y ≤ l ∧
      v = robustProduct b lam (fun i => (y i : ℝ)) (cardinalityAttacks k)
        (cardinalityAttacks_nonempty k)}
      (robustProduct b lam (fun i => (x i : ℝ))
        (cardinalityAttacks (min (Fintype.card ι) (k+l)))
        (cardinalityAttacks_nonempty _)) := by
  have hf := monotone_affineProduct b lam hb hl
  have hh := trimCompletion_isLeast l _ (monotone_trimCompletion k _ hf) x
  rw [trimCompletion_composition k l _ hf] at hh
  simpa only [product_completion] using hh

end
end EvidenceFusion
