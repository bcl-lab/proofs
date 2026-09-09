import FinnerMonitoring
import RepeatedEvidenceCalculus
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.Compact

open Set Filter MeasureTheory
open scoped BigOperators Topology

namespace RepeatedEvidence

/-- The exact differentiated objective is strictly convex on its whole domain. -/
theorem finnerTerm_strictConvex (a : ℝ) (ha : 0 < a) :
    StrictConvexOn ℝ (Ioi a) (finnerTerm a) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi a)
  · intro b hb
    exact (finner_first_derivative a b ha hb).continuousAt.continuousWithinAt
  · intro b hb
    have hb : a < b := by simpa using hb
    have he : EqOn (deriv (finnerTerm a)) (finnerFirst a) (Ioi a) := by
      intro x hx
      exact (finner_first_derivative a x ha hx).deriv
    have hd : HasDerivAt (deriv (finnerTerm a)) (a^2/(b*(b-a)^2)) b :=
      (finner_second_derivative a b ha hb).congr_of_eventuallyEq
        (he.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hb))
    change 0 < deriv (deriv (finnerTerm a)) b
    rw [hd.deriv]
    exact finner_curvature_positive a b ha hb

theorem finnerTerm_nonnegative (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    0 ≤ finnerTerm a b := by
  have hb : 0 < b := ha.trans hab
  have hq : 0 < 1-a/b := sub_pos.mpr ((div_lt_one hb).2 hab)
  have hl : Real.log (1-a/b) ≤ 0 := Real.log_nonpos hq.le (by
    have := div_pos ha hb
    linarith)
  exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hb.le hl)

/-- An explicit positive distance from the singular boundary, obtained
from an objective sublevel. This replaces an informal coercivity argument. -/
theorem finnerTerm_sublevel_margin (a b C : ℝ) (ha : 0 < a) (hab : a < b)
    (hC : finnerTerm a b ≤ C) :
    a + a * Real.exp (-C/a) ≤ b := by
  have hb : 0 < b := ha.trans hab
  have hq : 0 < 1-a/b := sub_pos.mpr ((div_lt_one hb).2 hab)
  have hl : Real.log (1-a/b) ≤ 0 := Real.log_nonpos hq.le (by
    have := div_pos ha hb
    linarith)
  have hsmall : -a * Real.log (1-a/b) ≤ C := by
    unfold finnerTerm at hC
    nlinarith [mul_nonneg (sub_pos.mpr hab).le (neg_nonneg.mpr hl)]
  have hlog : -C/a ≤ Real.log (1-a/b) := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have he : Real.exp (-C/a) ≤ 1-a/b := by
    simpa only [Real.exp_log hq] using Real.exp_le_exp.mpr hlog
  have hmul := mul_le_mul_of_nonneg_left he hb.le
  have hprod : b * (1-a/b) = b-a := by field_simp
  rw [hprod] at hmul
  have hmono := mul_le_mul_of_nonneg_right hab.le (Real.exp_pos (-C/a)).le
  linarith

def finnerDomain {V I : Type} [Fintype I] (A : V → I → Prop) [DecidableRel A]
    (a : I → ℝ) : Set (I → ℝ) :=
  {b | (∀ i, a i < b i) ∧ (∀ v, (∑ i, if A v i then b i else 0) ≤ 1)}

noncomputable def finnerObjective {I : Type} [Fintype I] (a b : I → ℝ) : ℝ :=
  ∑ i, finnerTerm (a i) (b i)

theorem finnerDomain_convex {V I : Type} [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) :
    Convex ℝ (finnerDomain A a) := by
  intro x hx y hy u v hu hv huv
  constructor
  · intro i
    exact (convex_Ioi (a i)) (hx.1 i) (hy.1 i) hu hv huv
  · intro w
    have he : (∑ i, if A w i then (u • x + v • y) i else 0) =
        u*(∑ i, if A w i then x i else 0) + v*(∑ i, if A w i then y i else 0) := by
      rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_left (hx.2 w) hu,
      mul_le_mul_of_nonneg_left (hy.2 w) hv]

theorem finnerObjective_strictConvex {V I : Type} [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 < a i) :
    StrictConvexOn ℝ (finnerDomain A a) (finnerObjective a) := by
  refine ⟨finnerDomain_convex A a, ?_⟩
  intro x hx y hy hxy u v hu hv huv
  have hcoord : ∃ i, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    simpa using (not_exists.mp h) i
  obtain ⟨j,hj⟩ := hcoord
  change (∑ i, finnerTerm (a i) (u*x i+v*y i)) <
    u*(∑ i, finnerTerm (a i) (x i)) + v*(∑ i, finnerTerm (a i) (y i))
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    exact (finnerTerm_strictConvex (a i) (ha i)).convexOn.2
      (hx.1 i) (hy.1 i) hu.le hv.le huv
  · exact ⟨j,Finset.mem_univ _, (finnerTerm_strictConvex (a j) (ha j)).2
      (hx.1 j) (hy.1 j) hj hu hv huv⟩

theorem finnerDomain_coord_le_one {V I : Type} [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a b : I → ℝ)
    (ha : ∀ i, 0 < a i) (hstudy : ∀ i, ∃ v, A v i) (hb : b ∈ finnerDomain A a)
    (i : I) : b i ≤ 1 := by
  classical
  obtain ⟨v,hv⟩ := hstudy i
  have hle : (if A v i then b i else 0) ≤ ∑ j, if A v j then b j else 0 :=
    Finset.single_le_sum (f := fun j => if A v j then b j else 0)
      (fun j _ => by dsimp only; split_ifs; exact (ha j).le.trans (hb.1 j).le; rfl)
      (Finset.mem_univ i)
  rw [if_pos hv] at hle
  exact hle.trans (hb.2 v)

/-- The finite objective attains a unique feasible minimum. The proof builds
a compact set separated from every singular face using the explicit margin,
and then applies the extreme value theorem and strict convexity. -/
theorem finnerObjective_exists_unique_minimum {V I : Type} [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (hstudy : ∀ i, ∃ v, A v i) (hne : (finnerDomain A a).Nonempty) :
    ∃! b, b ∈ finnerDomain A a ∧ IsMinOn (finnerObjective a) (finnerDomain A a) b := by
  classical
  obtain ⟨b₀,hb₀⟩ := hne
  let C := finnerObjective a b₀
  let lower (i : I) := a i + a i * Real.exp (-C/a i)
  let K : Set (I → ℝ) := Icc lower (fun _ => 1) ∩
    {b | ∀ v, (∑ i, if A v i then b i else 0) ≤ 1}
  have hlower (i : I) : a i < lower i := by
    dsimp [lower]
    exact lt_add_of_pos_right _ (mul_pos (ha i) (Real.exp_pos _))
  have hKD : K ⊆ finnerDomain A a := by
    intro b hb
    exact ⟨fun i => (hlower i).trans_le (hb.1.1 i),hb.2⟩
  have hsub (b : I → ℝ) (hb : b ∈ finnerDomain A a) (hval : finnerObjective a b ≤ C) :
      b ∈ K := by
    refine ⟨⟨?_,?_⟩,hb.2⟩
    · intro i
      apply finnerTerm_sublevel_margin (a i) (b i) C (ha i) (hb.1 i)
      exact (Finset.single_le_sum (fun j _ =>
        finnerTerm_nonnegative (a j) (b j) (ha j) (hb.1 j)) (Finset.mem_univ i)).trans hval
    · exact finnerDomain_coord_le_one A a b ha hstudy hb
  have hbK : b₀ ∈ K := hsub b₀ hb₀ le_rfl
  have hclosed : IsClosed {b : I → ℝ | ∀ v, (∑ i, if A v i then b i else 0) ≤ 1} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le _ continuous_const
    apply continuous_finset_sum
    intro i _
    split_ifs
    · exact continuous_apply i
    · exact continuous_const
  have hcompact : IsCompact K := isCompact_Icc.inter_right hclosed
  have hcont : ContinuousOn (finnerObjective a) K := by
    intro b hb
    apply ContinuousAt.continuousWithinAt
    apply tendsto_finset_sum
    intro i _
    exact (finner_first_derivative (a i) (b i) (ha i) ((hKD hb).1 i)).continuousAt.comp
      (f := fun c : I → ℝ => c i) (continuous_apply i).continuousAt
  obtain ⟨b,hb,hmin⟩ := hcompact.exists_isMinOn ⟨b₀,hbK⟩ hcont
  have hglobal : IsMinOn (finnerObjective a) (finnerDomain A a) b := by
    intro c hc
    by_cases hval : finnerObjective a c ≤ C
    · exact hmin (hsub c hc hval)
    · have h₀ : finnerObjective a b ≤ C := hmin hbK
      exact h₀.trans (le_of_not_ge hval)
  refine ⟨b,⟨hKD hb,hglobal⟩,?_⟩
  intro c hc
  exact (finnerObjective_strictConvex A a ha).eq_of_isMinOn hc.2 hglobal hc.1 (hKD hb)

/-- Subcritical source loads construct a nonempty feasible domain. -/
theorem finnerDomain_nonempty_of_subcritical {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (hload : ∀ v, RepeatedEvidenceProbability.sourceLoad A a v < 1) :
    (finnerDomain A a).Nonempty := by
  classical
  let s := insert (0:ℝ) (Finset.univ.image (RepeatedEvidenceProbability.sourceLoad A a))
  have hs : s.Nonempty := ⟨0,Finset.mem_insert_self _ _⟩
  let L : ℝ := (s.max' hs+1)/2
  have hmax : s.max' hs < 1 := by
    apply (Finset.max'_lt_iff s hs).2
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · norm_num
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hr
      exact hload v
  have hzero : 0 ≤ s.max' hs := Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  have hL0 : 0 < L := by dsimp [L]; linarith
  have hL1 : L < 1 := by dsimp [L]; linarith
  refine ⟨fun i => a i/L, ?_, ?_⟩
  · intro i
    apply (lt_div_iff₀ hL0).2
    nlinarith [ha i]
  · intro v
    have hv : RepeatedEvidenceProbability.sourceLoad A a v ≤ s.max' hs :=
      Finset.le_max' _ _ (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩))
    have he : (∑ i, if A v i then a i/L else 0) =
        RepeatedEvidenceProbability.sourceLoad A a v / L := by
      rw [RepeatedEvidenceProbability.sourceLoad,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [he]
    apply (div_le_one hL0).2
    dsimp [L]
    linarith

/-- The manuscript's global optimizer assertion, under its stated positive
powers, nonempty study-source sets and subcritical source loads. -/
theorem finner_subcritical_unique_optimizer {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 < a i)
    (hstudy : ∀ i, ∃ v, A v i)
    (hload : ∀ v, RepeatedEvidenceProbability.sourceLoad A a v < 1) :
    ∃! b, b ∈ finnerDomain A a ∧ IsMinOn (finnerObjective a) (finnerDomain A a) b :=
  finnerObjective_exists_unique_minimum A a ha hstudy
    (finnerDomain_nonempty_of_subcritical A a ha hload)

end RepeatedEvidence
