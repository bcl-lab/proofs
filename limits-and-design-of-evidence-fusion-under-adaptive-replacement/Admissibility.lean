import CompleteClass

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def DownwardClosed (A : Finset (Finset ι)) : Prop :=
  ∀ C ∈ A, ∀ B, B ⊆ C → B ∈ A

def positiveSupport (w : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => 0 < w i)

def projectedAttacks (A : Finset (Finset ι)) (w : ι → ℝ) : Finset (Finset ι) :=
  A.image (fun C => C ∩ positiveSupport w)

def MaximalProjected (A : Finset (Finset ι)) (w : ι → ℝ) (B : Finset ι) : Prop :=
  B ∈ projectedAttacks A w ∧ ∀ D ∈ projectedAttacks A w, B ⊆ D → D ⊆ B

def EmptyMaximalIntersection (A : Finset (Finset ι)) (w : ι → ℝ) : Prop :=
  ∀ i, ∃ B, MaximalProjected A w B ∧ i ∉ B

def AdmissibleRule (A : Finset (Finset ι)) (H : (ι → ℝ) → ℝ) : Prop :=
  FiniteRobustValid A H ∧ ∀ G : (ι → ℝ) → ℝ,
    (∀ y, (∀ i, 0 ≤ y i) → 0 ≤ G y) → FiniteRobustValid A G →
    (∀ y, (∀ i, 0 ≤ y i) → H y ≤ G y) →
    ∀ y, (∀ i, 0 ≤ y i) → G y = H y

theorem projected_subset_support (A : Finset (Finset ι)) (w : ι → ℝ)
    {B : Finset ι} (hB : B ∈ projectedAttacks A w) : B ⊆ positiveSupport w := by
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hB
  exact Finset.inter_subset_right

theorem projected_is_allowed (A : Finset (Finset ι)) (w : ι → ℝ)
    (hdown : DownwardClosed A) {B : Finset ι} (hB : B ∈ projectedAttacks A w) : B ∈ A := by
  obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hB
  exact hdown C hC _ Finset.inter_subset_left

theorem maximal_projected_extension (A : Finset (Finset ι)) (w : ι → ℝ)
    {C : Finset ι} (hC : C ∈ projectedAttacks A w) :
    ∃ B, MaximalProjected A w B ∧ C ⊆ B := by
  let s := (projectedAttacks A w).filter (fun B => C ⊆ B)
  have hs : s.Nonempty := ⟨C,by simp [s,hC]⟩
  obtain ⟨B,hB,hmax⟩ := Finset.exists_max_image s Finset.card hs
  have hBc := Finset.mem_filter.mp hB
  refine ⟨B,⟨hBc.1,?_⟩,hBc.2⟩
  intro D hD hBD
  have hDs : D ∈ s := Finset.mem_filter.mpr ⟨hD,hBc.2.trans hBD⟩
  have heq : B = D := Finset.eq_of_subset_of_card_le hBD (hmax D hDs)
  intro j hj
  rw [heq]
  exact hj

theorem keptSum_antitone_attacks (w y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, 0 ≤ y i)
    {B C : Finset ι} (hBC : B ⊆ C) : keptSum w y C ≤ keptSum w y B := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hiB : i ∈ B
  · simp [hiB,hBC hiB]
  · by_cases hiC : i ∈ C
    · simp only [hiC,hiB,if_true,if_false]
      exact mul_nonneg (hw i) (hy i)
    · simp [hiB,hiC]

theorem keptSum_projected (w y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (C : Finset ι) :
    keptSum w y (C ∩ positiveSupport w) = keptSum w y C := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ C
  · by_cases hp : 0 < w i
    · simp [hi,positiveSupport,hp]
    · have hz : w i = 0 := le_antisymm (le_of_not_gt hp) (hw i)
      simp [hi,positiveSupport,hp,hz]
  · simp [hi]

theorem exposing_configuration (A : Finset (Finset ι)) (hA : A.Nonempty)
    (hdown : DownwardClosed A) (a : ℝ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (i : ι) (hi : 0 < w i)
    (B : Finset ι) (hB : MaximalProjected A w B) (hiB : i ∉ B)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ y : ι → ℝ, (∀ j, 0 ≤ y j) ∧
      robustAffine a w y A hA = a + w i*t ∧
      ∀ v : ι → ℝ, keptSum v y B = v i*t := by
  have hBA : B ∈ A := projected_is_allowed A w hdown hB.1
  have hBs := projected_subset_support A w hB.1
  let y : ι → ℝ := fun j => if j = i then t else
    if j ∈ B then (w i*t+1)/w j else 0
  have hy (j : ι) : 0 ≤ y j := by
    dsimp [y]
    split_ifs with hj hBj
    · exact ht
    · exact div_nonneg (by positivity) (hw j)
    · exact le_rfl
  have hsum (v : ι → ℝ) : keptSum v y B = v i*t := by
    unfold keptSum
    rw [Finset.sum_eq_single i]
    · simp [y,hiB]
    · intro j _ hji
      by_cases hjB : j ∈ B <;> simp [y,hji,hjB]
    · simp
  refine ⟨y,hy,?_,hsum⟩
  apply le_antisymm
  · exact add_le_add_left ((Finset.inf'_le _ hBA).trans_eq (hsum w)) a
  · apply add_le_add_left
    apply Finset.le_inf'
    intro C hC
    by_cases hBC : B ⊆ C
    · have hiC : i ∉ C := by
        intro hIC
        have hproj : C ∩ positiveSupport w ∈ projectedAttacks A w :=
          Finset.mem_image.mpr ⟨C,hC,rfl⟩
        have hsub : B ⊆ C ∩ positiveSupport w := Finset.subset_inter hBC hBs
        apply hiB
        exact hB.2 _ hproj hsub (by simp [hIC,positiveSupport,hi])
      have hh := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset ι)) => show
          0 ≤ (if j ∈ C then 0 else w j*y j) by
            split_ifs; exact le_rfl; exact mul_nonneg (hw j) (hy j))
        (Finset.mem_univ i)
      simpa [hiC,y,keptSum] using hh
    · obtain ⟨j,hjB,hjC⟩ := Finset.not_subset.mp hBC
      have hwj : 0 < w j := by simpa [positiveSupport] using hBs hjB
      have hji : j ≠ i := fun he => hiB (he ▸ hjB)
      have hh := Finset.single_le_sum
        (fun j (_ : j ∈ (Finset.univ : Finset ι)) => show
          0 ≤ (if j ∈ C then 0 else w j*y j) by
            split_ifs; exact le_rfl; exact mul_nonneg (hw j) (hy j))
        (Finset.mem_univ j)
      have he : w j*y j = w i*t+1 := by
        simp only [y,if_neg hji,if_pos hjB]
        field_simp
      simp only [if_neg hjC,he] at hh
      exact (by linarith : w i*t ≤ w i*t+1).trans hh

theorem admissible_of_empty_maximal_intersection
    (A : Finset (Finset ι)) (hA : A.Nonempty) (hdown : DownwardClosed A)
    (a : ℝ) (w : ι → ℝ) (ha : 0 ≤ a) (hw : ∀ i, 0 ≤ w i)
    (hn : a + ∑ i, w i = 1) (hex : EmptyMaximalIntersection A w) :
    AdmissibleRule A (fun y => robustAffine a w y A hA) := by
  have hnonneg := fun y hy => robustAffine_nonneg a w y A hA ha hw hy
  have hvalid : FiniteRobustValid A (fun y => robustAffine a w y A hA) :=
    (complete_class_finite A hA _ hnonneg).mpr ⟨a,w,ha,hw,hn,fun _ _ => le_rfl⟩
  refine ⟨hvalid,?_⟩
  intro G hGn hG hHG
  obtain ⟨b,v,hb,hv,hbn,hGv⟩ := (complete_class_finite A hA G hGn).mp hG
  have hab : a ≤ b := by
    have hh := (hHG 0 (by simp)).trans (hGv 0 (by simp))
    simpa [robustAffine,keptSum] using hh
  have hwv (i : ι) : w i ≤ v i := by
    by_cases hi : 0 < w i
    · obtain ⟨B,hB,hiB⟩ := hex i
      apply slope_comparison (a := a) (b := b)
      intro t ht
      obtain ⟨y,hy,he,hattack⟩ := exposing_configuration A hA hdown a w hw i hi B hB hiB t ht
      have hh := (hHG y hy).trans (hGv y hy)
      change robustAffine a w y A hA ≤ robustAffine b v y A hA at hh
      rw [he] at hh
      have hBA := projected_is_allowed A w hdown hB.1
      have hvbound : robustAffine b v y A hA ≤ b + v i*t :=
        add_le_add_left ((Finset.inf'_le _ hBA).trans_eq (hattack v)) b
      exact hh.trans hvbound
    · exact (le_of_not_gt hi).trans (hv i)
  have hsum : ∑ i, w i ≤ ∑ i, v i := Finset.sum_le_sum fun i _ => hwv i
  have hba : b = a := by linarith
  have hwveq : w = v := normalized_coordinates_equal w v hwv (by linarith)
  intro y hy
  apply le_antisymm
  · simpa [hba,hwveq] using hGv y hy
  · exact hHG y hy

theorem erased_unavoidable_weight
    (A : Finset (Finset ι)) (hA : A.Nonempty) (hdown : DownwardClosed A)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (i : ι)
    (hi : ∀ B, MaximalProjected A w B → i ∈ B)
    (y : ι → ℝ) (hy : ∀ j, 0 ≤ y j) :
    A.inf' hA (keptSum (Function.update w i 0) y) = A.inf' hA (keptSum w y) := by
  let v := Function.update w i 0
  have hv (j : ι) : 0 ≤ v j := by
    by_cases hj : j = i <;> simp [v,hj,hw]
  have hvw (j : ι) : v j ≤ w j := by
    by_cases hj : j = i <;> simp [v,hj,hw]
  apply le_antisymm
  · obtain ⟨C,hC,hmin⟩ := Finset.exists_mem_eq_inf' hA (keptSum w y)
    rw [hmin]
    apply (Finset.inf'_le _ hC).trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ C
    · simp [hj]
    · simp only [hj,if_false]
      exact mul_le_mul_of_nonneg_right (hvw j) (hy j)
  · obtain ⟨C,hC,hmin⟩ := Finset.exists_mem_eq_inf' hA (keptSum v y)
    change A.inf' hA (keptSum w y) ≤ A.inf' hA (keptSum v y)
    rw [hmin]
    have hproj : C ∩ positiveSupport w ∈ projectedAttacks A w :=
      Finset.mem_image.mpr ⟨C,hC,rfl⟩
    obtain ⟨B,hB,hCB⟩ := maximal_projected_extension A w hproj
    have hBA := projected_is_allowed A w hdown hB.1
    apply (Finset.inf'_le _ hBA).trans
    apply Finset.sum_le_sum
    intro j _
    by_cases hjB : j ∈ B
    · simp only [hjB,if_true]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (hv j) (hy j)
    · have hji : j ≠ i := fun he => hjB (he ▸ hi B hB)
      have hveq : v j = w j := by simp [v,hji]
      by_cases hjC : j ∈ C
      · have hnpos : ¬ 0 < w j := by
          intro hp
          exact hjB (hCB (by simp [hjC,positiveSupport,hp]))
        have hwz : w j = 0 := le_antisymm (le_of_not_gt hnpos) (hw j)
        simp [hjB,hjC,hwz]
      · simp [hjB,hjC,hveq]

/-- Exact criterion against all nonnegative competitors valid for finite laws.
The complete-class theorem transfers it to the measurable probability model. -/
theorem exact_admissibility
    (A : Finset (Finset ι)) (hA : A.Nonempty) (hdown : DownwardClosed A)
    (a : ℝ) (w : ι → ℝ) (ha : 0 ≤ a) (hw : ∀ i, 0 ≤ w i)
    (hn : a + ∑ i, w i = 1) :
    AdmissibleRule A (fun y => robustAffine a w y A hA) ↔
      EmptyMaximalIntersection A w := by
  constructor
  · intro hadm
    by_contra hnot
    simp only [EmptyMaximalIntersection,not_forall,not_exists,not_and,not_not] at hnot
    obtain ⟨i,hi⟩ := hnot
    have hA' := hA
    obtain ⟨C,hC⟩ := hA'
    have hproj : C ∩ positiveSupport w ∈ projectedAttacks A w :=
      Finset.mem_image.mpr ⟨C,hC,rfl⟩
    obtain ⟨B,hB,hCB⟩ := maximal_projected_extension A w hproj
    have hwi : 0 < w i := by
      simpa [positiveSupport] using projected_subset_support A w hB.1 (hi B hB)
    let v := Function.update w i 0
    let b := a + w i
    have hv (j : ι) : 0 ≤ v j := by
      by_cases hj : j = i <;> simp [v,hj,hw]
    have hb : 0 ≤ b := add_nonneg ha (hw i)
    have hsum : ∑ j, v j = (∑ j, w j) - w i := by
      have he : ∀ j, v j = w j - (if j = i then w i else 0) := by
        intro j; by_cases hj : j = i <;> simp [v,hj]
      simp_rw [he]
      simp [Finset.sum_sub_distrib]
    have hbn : b + ∑ j, v j = 1 := by dsimp [b]; rw [hsum]; linarith
    let G := fun y => robustAffine b v y A hA
    have hGn := fun y hy => robustAffine_nonneg b v y A hA hb hv hy
    have hG : FiniteRobustValid A G :=
      (complete_class_finite A hA G hGn).mpr ⟨b,v,hb,hv,hbn,fun _ _ => le_rfl⟩
    have hshift (y : ι → ℝ) (hy : ∀ j, 0 ≤ y j) :
        G y = robustAffine a w y A hA + w i := by
      dsimp [G,robustAffine,b,v]
      rw [erased_unavoidable_weight A hA hdown w hw i hi y hy]
      ring
    have hdom (y : ι → ℝ) (hy : ∀ j, 0 ≤ y j) :
        robustAffine a w y A hA ≤ G y := by rw [hshift y hy]; linarith
    have he := hadm.2 G hGn hG hdom 0 (by simp)
    rw [hshift 0 (by simp)] at he
    linarith
  · exact admissible_of_empty_maximal_intersection A hA hdown a w ha hw hn

end
end EvidenceFusion
