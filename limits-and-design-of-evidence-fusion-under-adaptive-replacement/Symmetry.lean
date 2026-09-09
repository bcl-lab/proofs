import Cardinality

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hamming_permutation (x y : ι → ℝ) (σ : Equiv.Perm ι) :
    hamming (fun i => x (σ i)) (fun i => y (σ i)) = hamming x y := by
  have he : differences (fun i => x (σ i)) (fun i => y (σ i)) =
      (differences x y).map σ.symm.toEmbedding := by
    ext i
    simp [differences]
  simp [hamming,he]

theorem permutation_sum_constant (w : ι → ℝ) (i j : ι) :
    (∑ σ : Equiv.Perm ι, w (σ i)) = ∑ σ : Equiv.Perm ι, w (σ j) := by
  let e : Equiv.Perm (Equiv.Perm ι) :=
    { toFun := fun σ => (Equiv.swap i j).trans σ
      invFun := fun σ => (Equiv.swap i j).trans σ
      left_inv := by intro σ; ext k; simp
      right_inv := by intro σ; ext k; simp }
  have hh := Equiv.sum_comp e (fun σ => w (σ i))
  simpa [e,Equiv.trans_apply] using hh.symm

/-- The full symmetric complete-class domination, with constant coordinate
weight c. The normalization is equivalent to c = lambda/n and a = 1-lambda. -/
theorem symmetric_complete_class [Nonempty ι] (k : ℕ) (F : (ι → ℝ) → ℝ)
    (hFn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y)
    (hv : ProbabilityRobustValid (cardinalityAttacks k) F)
    (hsym : ∀ (σ : Equiv.Perm ι) y, F (fun i => y (σ i)) = F y) :
    ∃ a c : ℝ, 0 ≤ a ∧ 0 ≤ c ∧ a + (Fintype.card ι : ℝ)*c = 1 ∧
      ∀ y, (∀ i, 0 ≤ y i) →
        F y ≤ robustAffine a (fun _ => c) y (cardinalityAttacks k)
          (cardinalityAttacks_nonempty k) := by
  obtain ⟨a,w,ha,hw,hn,hdom⟩ := complete_affine_converse _ (cardinalityAttacks_nonempty k)
    F hFn ((finite_iff_probability_valid _ (cardinalityAttacks_nonempty k) F hFn).mpr hv)
  let P : ℝ := Fintype.card (Equiv.Perm ι)
  have hP : 0 < P := by dsimp [P]; exact_mod_cast Fintype.card_pos
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  let c : ℝ := (∑ σ : Equiv.Perm ι, w (σ i0))/P
  have hc : 0 ≤ c := div_nonneg (Finset.sum_nonneg fun σ _ => hw (σ i0)) hP.le
  have hW (i : ι) : (∑ σ : Equiv.Perm ι, w (σ i)) = P*c := by
    rw [permutation_sum_constant w i i0]
    dsimp [c]
    field_simp
  have hnorm : a + (Fintype.card ι : ℝ)*c = 1 := by
    have hh : (∑ i, ∑ σ : Equiv.Perm ι, w (σ i)) = P * ∑ i, w i := by
      rw [Finset.sum_comm]
      simp_rw [Equiv.sum_comp]
      simp [P]
    simp_rw [hW] at hh
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
    apply (mul_left_cancel₀ hP.ne')
    nlinarith [hn]
  have havg (x y : ι → ℝ) (hxy : Compatible (cardinalityAttacks k) x y) :
      F y ≤ a + ∑ i, c*x i := by
    have hb (σ : Equiv.Perm ι) : F y ≤ a + ∑ i, w (σ i)*x i := by
      have hhxy : Compatible (cardinalityAttacks k)
          (fun i => x (σ.symm i)) (fun i => y (σ.symm i)) := by
        rw [compatible_cardinality] at hxy ⊢
        exact ⟨fun i => hxy.1 _,fun i => hxy.2.1 _,by
          simpa [hamming_permutation] using hxy.2.2⟩
      have hh := hdom _ _ hhxy
      rw [hsym] at hh
      have he := Equiv.sum_comp σ (fun i => w i*x (σ.symm i))
      simp only [Equiv.symm_apply_apply] at he
      rwa [← he] at hh
    have hh := Finset.sum_le_sum (fun (σ : Equiv.Perm ι) (_ : σ ∈ Finset.univ) => hb σ)
    have he : (∑ σ : Equiv.Perm ι, (a + ∑ i, w (σ i)*x i)) =
        P * (a + ∑ i, c*x i) := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp_rw [← Finset.sum_mul,hW]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rw [mul_add,Finset.mul_sum]
      dsimp [P]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he] at hh
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
    exact (mul_le_mul_left hP).mp hh
  refine ⟨a,c,ha,hc,hnorm,?_⟩
  intro y hy
  unfold robustAffine
  apply (sub_le_iff_le_add').mp
  apply Finset.le_inf'
  intro C hC
  let x : ι → ℝ := fun i => if i ∈ C then 0 else y i
  have hxy : Compatible (cardinalityAttacks k) x y := by
    refine ⟨?_,hy,C,hC,?_⟩
    · intro i; dsimp [x]; split_ifs; exact le_rfl; exact hy i
    · intro i hi; simp [x,hi]
  have hh := havg x y hxy
  have he : (∑ i, c*x i) = keptSum (fun _ => c) y C := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ C <;> simp [x,hi]
  rw [he] at hh
  linarith

theorem symmetric_rule_admissible (k : ℕ) (hk : k < Fintype.card ι)
    (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hn : a + (Fintype.card ι : ℝ)*c = 1) :
    ProbabilityAdmissible (cardinalityAttacks (ι := ι) k)
      (fun y => robustAffine a (fun _ => c) y (cardinalityAttacks k)
        (cardinalityAttacks_nonempty k)) := by
  apply (cardinality_admissibility k a (fun _ : ι => c) ha (fun _ => hc) (by simpa using hn)).mpr
  rcases eq_or_lt_of_le hc with hz | hp
  · left; simp [positiveSupport,← hz]
  · right; simpa [positiveSupport,hp] using hk

end
end EvidenceFusion
