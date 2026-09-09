import MinimaxCapacity

open scoped BigOperators NNReal
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sorted_positive_extraction (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hne : ∃ i, 0 < x i) :
    ∃ p : ℕ, 0 < p ∧ ∃ e : Fin p ↪ ι,
      (∀ j, 0 < x (e j)) ∧ Antitone (fun j => x (e j)) ∧
      (∀ i, (¬ ∃ j, e j=i) → x i=0) := by
  let S := {i : ι // 0 < x i}
  letI : Nonempty S := by obtain ⟨i,hi⟩ := hne; exact ⟨⟨i,hi⟩⟩
  let p := Fintype.card S
  let f : Fin p ≃ S := (Fintype.equivFin S).symm
  let σ := descendingPermutation (fun j => x (f j).val)
  let e : Fin p ↪ ι := ⟨fun j => (f (σ j)).val,
    Subtype.val_injective.comp (f.injective.comp σ.injective)⟩
  refine ⟨p,Fintype.card_pos,e,fun j => (f (σ j)).property,?_,?_⟩
  · exact descendingPermutation_antitone (fun j => x (f j).val)
  · intro i hi
    apply le_antisymm _ (hx i)
    by_contra hn
    have hp : 0 < x i := lt_of_not_ge hn
    apply hi
    refine ⟨σ.symm (f.symm ⟨i,hp⟩),?_⟩
    simp [e]

theorem zero_vector_capacity (x : ι → ℝ≥0) (hx : ∀ i, (x i : ℝ)=0) (k l : ℕ) :
    IsGreatest (capacityValues k l x) 1 := by
  constructor
  · refine ⟨fun _ => 1,fun _ _ => by norm_num,?_,(worstValue_constant_one x l).symm⟩
    apply (complete_class_probability _ (cardinalityAttacks_nonempty k) _
      (fun _ _ => by norm_num)).mpr
    refine ⟨1,fun _ => 0,by norm_num,fun _ => le_rfl,by simp,?_⟩
    intro y _
    simp [robustAffine,keptSum]
  · rintro v ⟨F,hFn,hF,rfl⟩
    obtain ⟨a,w,ha,hw,hn,hdom⟩ := (complete_class_probability _ (cardinalityAttacks_nonempty k)
      F hFn).mp hF
    have hh := worstValue_mono F _ hFn hdom x l
    rw [robustAffine_worst_value k l a w hw x] at hh
    have he : trimmedSum (fun i => w i*(x i : ℝ)) (min (Fintype.card ι) (k+l))=0 := by
      simp [hx,trimmedSum,largestSum]
    rw [he,add_zero] at hh
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hw i)
    linarith

theorem capacity_admissible_attainment {p : ℕ} [NeZero p] (e : Fin p ↪ ι)
    (x : ι → ℝ≥0) (hpos : ∀ j, 0 < (x (e j) : ℝ))
    (hzero : ∀ i, (¬ ∃ j, e j=i) → (x i : ℝ)=0) (k l : ℕ) (hk : k ≤ Fintype.card ι) :
    ∃ F : (ι → ℝ) → ℝ, Continuous F ∧ (∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y) ∧
      ProbabilityAdmissible (cardinalityAttacks k) F ∧
      worstValue F x l = max 1
        (positiveCapacity (fun j => (x (e j) : ℝ)) (min (Fintype.card ι) (k+l))) := by
  let r := min (Fintype.card ι) (k+l)
  let c := positiveCapacity (fun j => (x (e j) : ℝ)) r
  have hkr : k ≤ r := le_min hk (Nat.le_add_right _ _)
  by_cases hc : c ≤ 1
  · have hAdm := (cardinality_admissibility k 1 (fun _ : ι => 0) (by norm_num)
      (fun _ => le_rfl) (by simp)).mpr (Or.inl (by simp [positiveSupport]))
    have he : (fun y => robustAffine 1 (fun _ : ι => 0) y (cardinalityAttacks k)
      (cardinalityAttacks_nonempty k)) = fun _ => (1 : ℝ) := by
      funext y; simp [robustAffine,keptSum]
    rw [he] at hAdm
    refine ⟨fun _ => 1,continuous_const,fun _ _ => by norm_num,hAdm,?_⟩
    change worstValue (fun _ => 1) x l=max 1 c
    rw [worstValue_constant_one,max_eq_left hc]
  · obtain ⟨w,hw,hs,hvalue⟩ := nonnegative_capacity_attained e (fun i => (x i : ℝ))
      (fun i => (x i).coe_nonneg) hpos hzero r
    have hcn : 0 < c := lt_trans (by norm_num) (lt_of_not_ge hc)
    have hp := trimmedSum_positive_support (fun i => w i*(x i : ℝ))
      (fun i => mul_nonneg (hw i) (x i).coe_nonneg) r (by simpa only [hvalue] using hcn)
    have hsub : positiveSupport (fun i => w i*(x i : ℝ)) ⊆ positiveSupport w := by
      intro i hi
      have hi' : 0 < w i*(x i : ℝ) := by simpa [positiveSupport] using hi
      have hwi : 0 < w i := lt_of_le_of_ne (hw i) (by
        intro he; rw [← he,zero_mul] at hi'; exact (lt_irrefl 0) hi')
      simpa [positiveSupport] using hwi
    refine ⟨fun y => robustAffine 0 w y (cardinalityAttacks k) (cardinalityAttacks_nonempty k),
      continuous_robustAffine _ _ 0 w,
      fun y hy => robustAffine_nonneg 0 w y _ _ le_rfl hw hy,?_,?_⟩
    · apply (cardinality_admissibility k 0 w le_rfl hw (by simpa using hs)).mpr
      exact Or.inr (hkr.trans_lt (hp.trans_le (Finset.card_le_card hsub)))
    · rw [robustAffine_worst_value k l 0 w hw x,zero_add]
      change trimmedSum (fun i => w i*(x i : ℝ)) r=max 1 c
      rw [hvalue,max_eq_right (le_of_not_ge hc)]

/-- The same attained optimum for the paper's Borel-measurable rule class. -/
theorem pointwise_capacity_borel {p : ℕ} [NeZero p] (e : Fin p ↪ ι) (x : ι → ℝ≥0)
    (hpos : ∀ j, 0 < (x (e j) : ℝ)) (hsort : Antitone (fun j => (x (e j) : ℝ)))
    (hzero : ∀ i, (¬ ∃ j, e j=i) → (x i : ℝ)=0) (k l : ℕ) (hk : k ≤ Fintype.card ι) :
    IsGreatest {v | ∃ F : (ι → ℝ) → ℝ, Measurable F ∧
      (∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y) ∧ ProbabilityRobustValid (cardinalityAttacks k) F ∧
      v=worstValue F x l} (max 1
        (positiveCapacity (fun j => (x (e j) : ℝ)) (min (Fintype.card ι) (k+l)))) := by
  constructor
  · obtain ⟨F,hFc,hFn,hF,hvalue⟩ := capacity_admissible_attainment e x hpos hzero k l hk
    exact ⟨F,hFc.measurable,hFn,hF.1,hvalue.symm⟩
  · rintro v ⟨F,_,hFn,hF,rfl⟩
    exact capacity_upper e x hpos hsort hzero k l F hFn hF

end
end EvidenceFusion
