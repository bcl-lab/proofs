import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
Formal proof components for Limits and design of evidence fusion under
adaptive replacement. The coverage report specifies which paper statements
are completely covered and which require additional bridges.
-/

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace EvidenceFusion

noncomputable section

section Static
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def keptSum (w x : ι → ℝ) (C : Finset ι) : ℝ :=
  ∑ i, if i ∈ C then 0 else w i * x i

def robustAffine (a : ℝ) (w x : ι → ℝ)
    (A : Finset (Finset ι)) (hA : A.Nonempty) : ℝ :=
  a + A.inf' hA (keptSum w x)

theorem keptSum_nonneg (w x : ι → ℝ) (C : Finset ι)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ keptSum w x C := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hw i) (hx i)

theorem keptSum_le_clean (w x y : ι → ℝ) (C : Finset ι)
    (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    (hclean : ∀ i, i ∉ C → y i = x i) :
    keptSum w y C ≤ ∑ i, w i * x i := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ C
  · simp only [hi, if_true]
    exact mul_nonneg (hw i) (hx i)
  · simp only [hi, if_false, hclean i hi]
    exact le_rfl

theorem robustAffine_nonneg (a : ℝ) (w y : ι → ℝ)
    (A : Finset (Finset ι)) (hA : A.Nonempty)
    (ha : 0 ≤ a) (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, 0 ≤ y i) :
    0 ≤ robustAffine a w y A hA := by
  exact add_nonneg ha (Finset.le_inf' hA _ fun C _ => keptSum_nonneg w y C hw hy)

/-- Pathwise validity inequality in Theorem S1. The attack may depend on x. -/
theorem robustAffine_le_clean (a : ℝ) (w x y : ι → ℝ)
    (A : Finset (Finset ι)) (hA : A.Nonempty) (C : Finset ι)
    (hC : C ∈ A) (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    (hclean : ∀ i, i ∉ C → y i = x i) :
    robustAffine a w y A hA ≤ a + ∑ i, w i * x i := by
  exact add_le_add_left ((Finset.inf'_le _ hC).trans
    (keptSum_le_clean w x y C hw hx hclean)) a

/-- The weight-budget step, also used after conditional expectation. -/
theorem normalized_weight_bound (a : ℝ) (w m : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : ∀ i, m i ≤ 1)
    (hnorm : a + ∑ i, w i = 1) :
    a + ∑ i, w i * m i ≤ 1 := by
  calc
    a + ∑ i, w i * m i ≤ a + ∑ i, w i * 1 := by
      apply add_le_add_left
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hm i) (hw i)
    _ = 1 := by simpa using hnorm

/-- Arbitrary finite probability spaces, with attacks varying by outcome. -/
theorem finite_probability_validity {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (F : Ω → ℝ) (X : Ω → ι → ℝ)
    (a : ℝ) (w : ι → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (hw : ∀ i, 0 ≤ w i) (hnorm : a + ∑ i, w i = 1)
    (hmean : ∀ i, ∑ ω, p ω * X ω i ≤ 1)
    (hdom : ∀ ω, F ω ≤ a + ∑ i, w i * X ω i) :
    ∑ ω, p ω * F ω ≤ 1 := by
  calc
    ∑ ω, p ω * F ω ≤ ∑ ω, p ω * (a + ∑ i, w i * X ω i) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left (hdom ω) (hp ω)
    _ = a + ∑ i, w i * (∑ ω, p ω * X ω i) := by
      simp_rw [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hp1, one_mul, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ 1 := normalized_weight_bound a w _ hw hmean hnorm

/-- Slope extraction in the admissibility proof, with no limiting argument. -/
theorem slope_comparison {a b w v : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → a + w*t ≤ b + v*t) : w ≤ v := by
  by_contra hn
  have hd : 0 < w-v := by linarith
  have hab : a ≤ b := by simpa using h 0 (by norm_num)
  have ht : 0 ≤ (b-a+1)/(w-v) := div_nonneg (by linarith) hd.le
  have hh := h ((b-a+1)/(w-v)) ht
  have he : (w-v)*((b-a+1)/(w-v)) = b-a+1 := by field_simp
  nlinarith

/-- Normalization forces equality once every component is bounded below. -/
theorem normalized_coordinates_equal (w v : ι → ℝ)
    (h : ∀ i, w i ≤ v i) (hs : ∑ i, v i = ∑ i, w i) : w = v := by
  funext i
  have hz : ∑ j, (v j - w j) = 0 := by rw [Finset.sum_sub_distrib, hs]; ring
  have hnonneg : ∀ j ∈ (Finset.univ : Finset ι), 0 ≤ v j-w j := by
    intro j _; exact sub_nonneg.mpr (h j)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz i (Finset.mem_univ i)
  linarith
end Static

section Rank
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def upperRank (s : ι → ℝ) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => s i ≤ s j).card

/-- Tie-conservative rank counting, valid for every finite score vector. -/
theorem rank_count_le (s : ι → ℝ) (q : ℕ) :
    (Finset.univ.filter fun i => upperRank s i ≤ q).card ≤ q := by
  let good := Finset.univ.filter fun i => upperRank s i ≤ q
  by_cases hne : good.Nonempty
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image good s hne
    have hsub : good ⊆ Finset.univ.filter (fun j => s i ≤ s j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmin j hj⟩
    exact (Finset.card_le_card hsub).trans (Finset.mem_filter.mp hi).2
  · have he : good = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change good.card ≤ q
    simp [he]

/-- Decreasing the attacked test score only increases its upper-tail rank. -/
theorem attacked_rank_ge (z : ι → ℝ) (test upper : ℝ) (h : test ≤ upper) :
    1 + (Finset.univ.filter fun i => upper ≤ z i).card ≤
    1 + (Finset.univ.filter fun i => test ≤ z i).card := by
  apply Nat.add_le_add_left
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h.trans (Finset.mem_filter.mp hi).2⟩

/-- The finite-sample resolution requirement used in S14. -/
theorem five_percent_resolution (m r : ℕ) (hr : 1 ≤ r)
    (h : (r : ℝ) / (m+1) ≤ 1/20) : 19 ≤ m := by
  have hd : (0 : ℝ) < m+1 := by positivity
  have hh := (div_le_iff₀ hd).mp h
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm : (19 : ℝ) ≤ m := by linarith
  exact_mod_cast hm
end Rank

section Capacity

/-- The paper's single-swap rearrangement calculation. -/
theorem reciprocal_swap (xi xj vi vj : ℝ)
    (_hxi : 0 < xi) (hxj : 0 < xj) (hx : xj ≤ xi) (hv : vi ≤ vj) :
    vj/xi + vi/xj ≤ vi/xi + vj/xj := by
  have hinv : 1/xi ≤ 1/xj := one_div_le_one_div_of_le hxj hx
  have hmul := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hv) (sub_nonpos.mpr hinv)
  simp only [div_eq_mul_inv, one_mul] at *
  nlinarith

/-- The layer bound in S13, for arbitrary nonnegative layers. -/
theorem layer_capacity_bound {ι : Type*} [Fintype ι]
    (d A b : ι → ℝ) (c : ℝ)
    (hd : ∀ j, 0 ≤ d j) (hc : 0 ≤ c)
    (hratio : ∀ j, b j ≤ c * A j)
    (hcost : ∑ j, d j * A j ≤ 1) :
    ∑ j, d j * b j ≤ c := by
  calc
    ∑ j, d j * b j ≤ ∑ j, d j * (c * A j) := by
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hratio j) (hd j)
    _ = c * ∑ j, d j * A j := by rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hcost hc
    _ = c := mul_one c

/-- The bounded-evidence necessary report count, before integer rounding. -/
theorem report_count_necessary (p k B T : ℝ)
    (hp : 0 < p) (hBT : T < B)
    (hcapacity : T ≤ B * (1 - 2*k/p)) :
    2*k*B/(B-T) ≤ p := by
  apply (div_le_iff₀ (sub_pos.mpr hBT)).mpr
  have hmul := mul_le_mul_of_nonneg_right hcapacity hp.le
  have he : B * (1-2*k/p)*p = B*(p-2*k) := by field_simp
  rw [he] at hmul
  nlinarith

theorem equal_signal_threshold_iff (p k B T : ℝ)
    (hp : 0 < p) (hBT : T < B) :
    T ≤ B*(1-2*k/p) ↔ 2*k*B/(B-T) ≤ p := by
  constructor
  · exact report_count_necessary p k B T hp hBT
  · intro h
    have hh := (div_le_iff₀ (sub_pos.mpr hBT)).mp h
    apply (mul_le_mul_right hp).mp
    have he : B * (1-2*k/p)*p = B*(p-2*k) := by field_simp
    rw [he]
    nlinarith

theorem exact_report_examples :
    (50 : ℝ)*(1-2*1/3) < 20 ∧ 20 ≤ (50 : ℝ)*(1-2*1/4) ∧
    (50 : ℝ)*(1-2*3/9) < 20 ∧ (50 : ℝ)*(1-2*3/10) = 20 ∧
    (50 : ℝ)*(1-2*5/16) < 20 ∧ 20 ≤ (50 : ℝ)*(1-2*5/17) ∧
    (50 : ℝ)*(1-2*2/10) = 30 := by norm_num

theorem report_count_integer_criterion (p k : ℕ) (hp : 0 < p) :
    (20 : ℝ) ≤ 50*(1-2*k/p) ↔ 10*k ≤ 3*p := by
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  rw [equal_signal_threshold_iff (p:ℝ) (k:ℝ) 50 20 hpr (by norm_num)]
  constructor
  · intro h
    have hr : (10 : ℝ)*k ≤ 3*p := by
      have hh := (div_le_iff₀ (by norm_num : (0:ℝ) < 50-20)).mp h
      nlinarith
    exact_mod_cast hr
  · intro h
    have hr : (10 : ℝ)*k ≤ 3*p := by exact_mod_cast h
    apply (div_le_iff₀ (by norm_num : (0:ℝ) < 50-20)).mpr
    nlinarith

theorem sharp_integer_report_counts (p : ℕ) (hp : 0 < p) :
    ((20 : ℝ) ≤ 50*(1-2*1/p) ↔ 4 ≤ p) ∧
    ((20 : ℝ) ≤ 50*(1-2*3/p) ↔ 10 ≤ p) ∧
    ((20 : ℝ) ≤ 50*(1-2*5/p) ↔ 17 ≤ p) := by
  have h1 := report_count_integer_criterion p 1 hp
  have h3 := report_count_integer_criterion p 3 hp
  have h5 := report_count_integer_criterion p 5 hp
  constructor
  · convert h1 using 1 <;> norm_num <;> omega
  constructor
  · convert h3 using 1 <;> norm_num <;> omega
  · convert h5 using 1 <;> norm_num <;> omega

end Capacity

section SharpLayerProgram
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def layerOptimum (A b : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => b j / A j

/-- Full solution of the nonnegative layer optimization used in S13. -/
theorem sharp_layer_program (A b : ι → ℝ)
    (hA : ∀ j, 0 < A j) (hb : ∀ j, 0 ≤ b j) :
    (∀ d : ι → ℝ, (∀ j, 0 ≤ d j) → (∑ j, d j*A j ≤ 1) →
      ∑ j, d j*b j ≤ layerOptimum A b) ∧
    (∃ d : ι → ℝ, (∀ j, 0 ≤ d j) ∧ (∑ j, d j*A j = 1) ∧
      ∑ j, d j*b j = layerOptimum A b) := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j => b j / A j) Finset.univ_nonempty
  have heq : layerOptimum A b = b j/A j := by
    unfold layerOptimum
    apply le_antisymm
    · exact Finset.sup'_le Finset.univ_nonempty (fun j => b j/A j) hmax
    · exact Finset.le_sup' (fun j => b j/A j) hj
  constructor
  · intro d hd hcost
    apply layer_capacity_bound d A b (layerOptimum A b) hd
    · rw [heq]; exact div_nonneg (hb j) (hA j).le
    · intro i
      apply (div_le_iff₀ (hA i)).mp
      rw [heq]
      exact hmax i (Finset.mem_univ i)
    · exact hcost
  · refine ⟨fun i => if i=j then 1/A j else 0, ?_, ?_, ?_⟩
    · intro i; dsimp; split_ifs
      · exact (one_div_pos.mpr (hA j)).le
      · exact le_rfl
    · simp [ne_of_gt (hA j)]
    · simp [heq, div_eq_mul_inv, mul_comm]

/-- Exact change in reciprocal cost for an aligned permutation. -/
theorem rearranged_cost_le (v c : ι → ℝ) (σ : Equiv.Perm ι)
    (h : Antivary v c) :
    ∑ i, v i*c i ≤ ∑ i, v (σ i)*c i := by
  exact h.sum_mul_le_sum_comp_perm_mul

end SharpLayerProgram

section LayerIdentities
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- Finite Fubini gives the reciprocal-cost layer identity in S13. -/
theorem layer_cost_identity (d c : ι → ℝ) :
    (∑ i, (∑ j, if i ≤ j then d j else 0) * c i) =
    ∑ j, d j * (∑ i, if i ≤ j then c i else 0) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- The same identity for a selected retained tail. -/
theorem layer_tail_identity (d : ι → ℝ) (R : Finset ι) :
    (∑ i ∈ R, ∑ j, if i ≤ j then d j else 0) =
    ∑ j, d j * ((R.filter fun i => i ≤ j).card : ℝ) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [Finset.sum_ite, mul_comm]

end LayerIdentities

theorem normalization_example_arithmetic :
    (20 : ℝ)*(1/16)*(8/10) = 1 ∧
    (8*20 : ℝ)/10 = 16 ∧ (8*20 : ℝ)/8 = 20 ∧
    (1/20 : ℝ) < 1/16 := by norm_num

section Duality
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Weak game duality supporting S4, without assuming a saddle point. -/
theorem game_weak_duality (w : ι → ℝ) (q : κ → ℝ) (A : κ → ι → ℝ)
    (s r : ℝ) (hw : ∀ i, 0 ≤ w i) (hq : ∀ j, 0 ≤ q j)
    (hw1 : ∑ i, w i = 1) (hq1 : ∑ j, q j = 1)
    (hlower : ∀ i, s ≤ ∑ j, q j*A j i)
    (hupper : ∀ j, ∑ i, w i*A j i ≤ r) : s ≤ r := by
  calc
    s = ∑ i, w i*s := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ i, w i*(∑ j, q j*A j i) := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlower i) (hw i)
    _ = ∑ j, q j*(∑ i, w i*A j i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ j, q j*r := by
      exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hupper j) (hq j)
    _ = r := by rw [← Finset.sum_mul, hq1, one_mul]

end Duality

section ChangeOfMeasure
variable {Ω : Type*} [Fintype Ω]

/-- The finite-law tilt identities used in S9. Analytic differentiation and
the asymptotic upper bound are separate obligations. -/
theorem finite_tilt_identities (p x : Ω → ℝ) (lam : ℝ)
    (hL : ∀ ω, 1-lam+lam*x ω ≠ 0)
    (hp : ∑ ω, p ω = 1)
    (hd : ∑ ω, p ω*((x ω-1)/(1-lam+lam*x ω)) = 0) :
    (∑ ω, p ω/(1-lam+lam*x ω)) = 1 ∧
    (∑ ω, p ω*x ω/(1-lam+lam*x ω)) = 1 := by
  have hfirst : ∀ ω, p ω/(1-lam+lam*x ω) =
      p ω - lam*(p ω*((x ω-1)/(1-lam+lam*x ω))) := by
    intro ω
    field_simp [hL ω]
    <;> ring
  have hmass : (∑ ω, p ω/(1-lam+lam*x ω)) = 1 := by
    simp_rw [hfirst]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp, hd]
    ring
  refine ⟨hmass, ?_⟩
  calc
    _ = ∑ ω, (p ω/(1-lam+lam*x ω) + p ω*((x ω-1)/(1-lam+lam*x ω))) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = 1 := by rw [Finset.sum_add_distrib, hmass, hd, add_zero]

end ChangeOfMeasure

section Hamming
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]

def differences (x y : ι → α) : Finset ι :=
  Finset.univ.filter fun i => x i ≠ y i

def hamming (x y : ι → α) : ℕ := (differences x y).card

theorem hamming_le_dimension (x y : ι → α) : hamming x y ≤ Fintype.card ι := by
  exact Finset.card_filter_le _ _

theorem hamming_triangle (x y z : ι → α) :
    hamming x z ≤ hamming x y + hamming y z := by
  have hsub : differences x z ⊆ differences x y ∪ differences y z := by
    intro i hi
    simp only [differences, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union] at *
    by_cases h : x i = y i
    · right; intro hz; exact hi (h.trans hz)
    · exact Or.inl h
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The constructive midpoint step in Lemma S6, in every finite dimension. -/
theorem hamming_midpoint (x z : ι → α) (k l : ℕ)
    (h : hamming x z ≤ k+l) :
    ∃ y, hamming x y ≤ k ∧ hamming y z ≤ l := by
  let S := differences x z
  obtain ⟨A, hAS, hcard⟩ := Finset.exists_subset_card_eq (s := S) (min_le_right k S.card)
  let y : ι → α := fun i => if i ∈ A then z i else x i
  have hsub1 : differences x y ⊆ A := by
    intro i hi
    by_contra hiA
    have hne := (Finset.mem_filter.mp hi).2
    exact hne (by simp [y, hiA])
  have hsub2 : differences y z ⊆ S \ A := by
    intro i hi
    have hne := (Finset.mem_filter.mp hi).2
    have hiA : i ∉ A := by intro hiA; exact hne (by simp [y, hiA])
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hiA⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    simpa [y, hiA] using hne
  refine ⟨y, ?_, ?_⟩
  · exact (Finset.card_le_card hsub1).trans (hcard.le.trans (min_le_left _ _))
  · have hc := Finset.card_sdiff hAS
    have hbound : (S \ A).card ≤ l := by
      rw [hc, hcard]
      change S.card ≤ k+l at h
      omega
    exact (Finset.card_le_card hsub2).trans hbound

/-- Exact equality of the two-stage feasible relation and the capped ball. -/
theorem hamming_ball_composition (x z : ι → α) (k l : ℕ) :
    (∃ y, hamming x y ≤ k ∧ hamming y z ≤ l) ↔
    hamming x z ≤ min (Fintype.card ι) (k+l) := by
  constructor
  · rintro ⟨y, hk, hl⟩
    exact le_min (hamming_le_dimension x z)
      ((hamming_triangle x y z).trans (Nat.add_le_add hk hl))
  · intro h
    exact hamming_midpoint x z k l (h.trans (min_le_right _ _))

/-- Equality of the payoff sets whose infima appear in Lemma S6. -/
theorem completion_payoff_set (f : (ι → α) → ℝ) (x : ι → α) (k l : ℕ) :
    {v : ℝ | ∃ y z, hamming x y ≤ k ∧ hamming y z ≤ l ∧ f z = v} =
    {v : ℝ | ∃ z, hamming x z ≤ min (Fintype.card ι) (k+l) ∧ f z = v} := by
  ext v
  constructor
  · rintro ⟨y, z, hk, hl, hv⟩
    exact ⟨z, (hamming_ball_composition x z k l).mp ⟨y, hk, hl⟩, hv⟩
  · rintro ⟨z, hz, hv⟩
    obtain ⟨y, hk, hl⟩ := (hamming_ball_composition x z k l).mpr hz
    exact ⟨y, z, hk, hl, hv⟩

end Hamming

section Sequential
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def robustProduct (b lam y : ι → ℝ) (A : Finset (Finset ι))
    (hA : A.Nonempty) : ℝ :=
  A.inf' hA (fun C => ∏ i, if i ∈ C then b i else b i + lam i*y i)

/-- The pathwise product comparison in S5, including varying coefficients. -/
theorem replacement_product_bound (b lam x y : ι → ℝ) (C : Finset ι)
    (hb : ∀ i, 0 ≤ b i) (hl : ∀ i, 0 ≤ lam i) (hx : ∀ i, 0 ≤ x i)
    (hclean : ∀ i, i ∉ C → y i = x i) :
    (∏ i, if i ∈ C then b i else b i + lam i*y i) ≤
    ∏ i, (b i + lam i*x i) := by
  apply Finset.prod_le_prod
  · intro i _
    by_cases hi : i ∈ C
    · simpa [hi] using hb i
    · simp only [hi, if_false, hclean i hi]
      exact add_nonneg (hb i) (mul_nonneg (hl i) (hx i))
  · intro i _
    by_cases hi : i ∈ C
    · simp only [hi, if_true]
      exact le_add_of_nonneg_right (mul_nonneg (hl i) (hx i))
    · simp only [hi, if_false, hclean i hi]
      exact le_rfl

/-- The full pathwise domination step of Theorem S5. -/
theorem robustProduct_domination (b lam x y : ι → ℝ)
    (A : Finset (Finset ι)) (hA : A.Nonempty) (C : Finset ι) (hC : C ∈ A)
    (hb : ∀ i, 0 ≤ b i) (hl : ∀ i, 0 ≤ lam i) (hx : ∀ i, 0 ≤ x i)
    (hclean : ∀ i, i ∉ C → y i = x i) :
    robustProduct b lam y A hA ≤ ∏ i, (b i + lam i*x i) := by
  exact (Finset.inf'_le _ hC).trans (replacement_product_bound b lam x y C hb hl hx hclean)

/-- A deterministic trimming bound used before the strong-law step in S8. -/
theorem sparse_trim_bound (z : ι → ℝ) (D : Finset ι) (A : ℝ)
    (hz : ∀ i, 0 ≤ z i) (hA : 0 ≤ A) :
    ∑ i ∈ D, z i ≤ A * D.card +
      ∑ i, if A < z i then z i else 0 := by
  calc
    ∑ i ∈ D, z i ≤ ∑ i ∈ D, (A + if A < z i then z i else 0) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with h
      · linarith
      · have hle : z i ≤ A := le_of_not_gt h
        simpa using hle
    _ = A * D.card + ∑ i ∈ D, if A < z i then z i else 0 := by
      rw [Finset.sum_add_distrib]
      simp [mul_comm]
    _ ≤ A * D.card + ∑ i, if A < z i then z i else 0 := by
      apply add_le_add_left
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ D)
      intro i _ _
      split_ifs
      · exact hz i
      · exact le_rfl

/-- Exact finite prior mass in the delayed mixture in S8. -/
theorem delayed_prior_mass (J : ℕ) :
    (∑ j ∈ Finset.range J, (1 : ℝ)/((j+1)*(j+2))) = 1-1/(J+1) := by
  induction J with
  | zero => norm_num
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : (J : ℝ)+1 ≠ 0 := by positivity
    have h2 : (J : ℝ)+2 ≠ 0 := by positivity
    field_simp
    <;> ring

/-- Bounded derivative factor supporting S7; no bounded-input assumption. -/
theorem log_factor_derivative_bound (x lam eps : ℝ)
    (hx : 0 ≤ x) (heps : 0 < eps)
    (hlow : eps ≤ lam) (hhigh : lam ≤ 1-eps) :
    |(x-1)/(1-lam+lam*x)| ≤ 1/eps := by
  have hlam : 0 ≤ lam := le_trans heps.le hlow
  have hd : 0 < 1-lam+lam*x := by nlinarith [mul_nonneg hlam hx]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ hd).mpr
    have hh : -(1/eps)*(1-lam+lam*x) ≤ x-1 := by
      apply (mul_le_mul_right heps).mp
      field_simp
      nlinarith [mul_nonneg hx (show 0 ≤ lam+eps by linarith)]
    exact hh
  · apply (div_le_iff₀ hd).mpr
    apply (mul_le_mul_right heps).mp
    field_simp
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hlow)]

/-- The reachability argument of S10 for deterministic finite histories. -/
theorem no_envelope_bound (t : ℕ) (stat : (Fin t → ℝ) → ℝ)
    (hvalid : ∀ y : ℕ → ℝ, (∀ i, 0 ≤ y i) →
      (∃ N, ∀ i, N ≤ i → y i = 0) → stat (fun i => y i) ≤ 1)
    (history : Fin t → ℝ) (hh : ∀ i, 0 ≤ history i) :
    stat history ≤ 1 := by
  let y : ℕ → ℝ := fun i => if h : i < t then history ⟨i,h⟩ else 0
  have hy : ∀ i, 0 ≤ y i := by
    intro i
    dsimp [y]
    split_ifs with h
    · exact hh ⟨i,h⟩
    · exact le_rfl
  have htail : ∃ N, ∀ i, N ≤ i → y i = 0 := by
    refine ⟨t, ?_⟩
    intro i hi
    simp [y, not_lt.mpr hi]
  have h := hvalid y hy htail
  have he : (fun i : Fin t => y i) = history := by funext i; simp [y, i.isLt]
  simpa [he] using h

end Sequential

end
end EvidenceFusion
