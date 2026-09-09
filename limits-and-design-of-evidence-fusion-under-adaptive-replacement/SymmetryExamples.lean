import Symmetry
import MinimaxCapacity

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

theorem trimmedSum_constant (n k : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    trimmedSum (fun _ : Fin n => u) k = ((n-min n k : ℕ) : ℝ)*u := by
  rw [trimmedSum,largestSum_sorted _ (fun _ => hu) (fun _ _ _ => le_rfl)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,headIndices_card,nsmul_eq_mul,
    Nat.cast_sub (Nat.min_le_left n k),sub_mul]

theorem uniform_permutation_mean {n : ℕ} [NeZero n] (u : Fin n → ℝ)
    (hs : ∑ i, u i=(n : ℝ)) (i : Fin n) :
    (∑ σ : Equiv.Perm (Fin n), (1/(Fintype.card (Equiv.Perm (Fin n)) : ℝ))*u (σ i))=1 := by
  let P : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hP : 0 < P := by dsimp [P]; exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < n := by exact_mod_cast NeZero.pos n
  have hh : (n : ℝ)*(∑ σ : Equiv.Perm (Fin n), u (σ i))=P*(n : ℝ) := by
    have he : (∑ j : Fin n, ∑ σ : Equiv.Perm (Fin n), u (σ j)) =
        ∑ j : Fin n, ∑ σ : Equiv.Perm (Fin n), u (σ i) := by
      apply Finset.sum_congr rfl
      intro j _
      exact permutation_sum_constant u j i
    rw [Finset.sum_comm] at he
    simp_rw [Equiv.sum_comp,hs] at he
    simpa [P] using he.symm
  have he : (∑ σ : Equiv.Perm (Fin n), u (σ i))=P := by nlinarith
  rw [← Finset.mul_sum,he]
  change (1/P)*P=1
  field_simp

/-- A complete finite probability counterexample for every 0 < m < n.
The clean law is the uniform permutation of m identical positive reports. -/
theorem adaptive_normalization_counterexample (n m : ℕ) (hm : 0 < m) (hmn : m < n) :
    ¬ FiniteRobustValid (cardinalityAttacks (n-m))
      (fun y : Fin n → ℝ => trimmedSum y (n-m)/(m : ℝ)) := by
  letI : NeZero n := ⟨by omega⟩
  let S := headIndices n m
  let v : ℝ := (n : ℝ)/(m : ℝ)
  let u := fun i : Fin n => if i ∈ S then v else 0
  let P : ℝ := Fintype.card (Equiv.Perm (Fin n))
  have hP : 0 < P := by dsimp [P]; exact_mod_cast Fintype.card_pos
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hnr : (m : ℝ) < n := by exact_mod_cast hmn
  have hv : 0 < v := div_pos (hmr.trans hnr) hmr
  have hScard : S.card=m := by rw [headIndices_card,Nat.min_eq_right hmn.le]
  have hus : ∑ i, u i=(n : ℝ) := by
    simp only [u,← Finset.sum_filter]
    simp [hScard,v]
    field_simp
  intro hvalid
  have hh := hvalid (Equiv.Perm (Fin n)) (fun _ => 1/P)
    (fun σ i => u (σ i)) (fun _ _ => v)
    (fun _ => (one_div_pos.mpr hP).le) (by simp [P])
    (fun σ => ?_) (fun i => uniform_permutation_mean u hus i |>.le)
  · have ht : trimmedSum (fun _ : Fin n => v) (n-m)/(m : ℝ)=v := by
      rw [trimmedSum_constant n (n-m) v hv.le,Nat.min_eq_right (Nat.sub_le _ _)]
      rw [Nat.sub_sub_self hmn.le]
      field_simp
    simp only [ht,← Finset.sum_mul] at hh
    have hp1 : (∑ _σ : Equiv.Perm (Fin n), 1/P)=1 := by simp [P]
    rw [hp1,one_mul] at hh
    have hv1 : 1 < v := (one_lt_div hmr).mpr hnr
    linarith
  · let D := S.map σ.symm.toEmbedding
    let C := Finset.univ \ D
    refine ⟨fun i => by dsimp [u]; split_ifs; exact hv.le; exact le_rfl,
      fun _ => hv.le,C,?_,?_⟩
    · apply (mem_cardinalityAttacks _ _).mpr
      dsimp [C,D]
      rw [Finset.card_sdiff (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
        Finset.card_map,hScard]
    · intro i hi
      have hiD : i ∈ D := by simpa [C] using hi
      have hiS : σ i ∈ S := by simpa [D] using hiD
      simp [u,hiS]

theorem symmetric_neutrality {n : ℕ} [NeZero n] (k : ℕ) (hk : 0 < k) (hkn : k < n)
    (F : (Fin n → ℝ) → ℝ) (hFn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y)
    (hv : ProbabilityRobustValid (cardinalityAttacks k) F)
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) y, F (fun i => y (σ i))=F y)
    (hneutral : F (fun _ => 1)=1) : ∀ y, (∀ i, 0 ≤ y i) → F y ≤ 1 := by
  obtain ⟨a,c,ha,hc,hn,hdom⟩ := symmetric_complete_class k F hFn hv hsym
  have hone := hdom (fun _ => 1) (fun _ => by norm_num)
  rw [hneutral,robustAffine_eq_trimmedSum] at hone
  simp only [mul_one,trimmedSum_constant n k c hc,Nat.min_eq_right hkn.le,
    Nat.cast_sub hkn.le,Fintype.card_fin] at hone hn
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hcz : c=0 := by nlinarith
  have haz : a=1 := by simpa [hcz] using hn
  intro y hy
  have hh := hdom y hy
  simpa [hcz,haz,robustAffine,keptSum] using hh

end
end EvidenceFusion
