import WorstPerformance

open scoped BigOperators NNReal
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem affine_probability_valid (k : ℕ) (a : ℝ) (w : ι → ℝ)
    (ha : 0 ≤ a) (hw : ∀ i, 0 ≤ w i) (hn : a+∑ i, w i=1) :
    ProbabilityRobustValid (cardinalityAttacks k)
      (fun y => robustAffine a w y (cardinalityAttacks k) (cardinalityAttacks_nonempty k)) := by
  apply (complete_class_probability _ _ _
    (fun y hy => robustAffine_nonneg a w y _ _ ha hw hy)).mpr
  exact ⟨a,w,ha,hw,hn,fun _ _ => le_rfl⟩

theorem nonnegative_capacity_attained {p : ℕ} [NeZero p] (e : Fin p ↪ ι)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hpos : ∀ j, 0 < x (e j))
    (hzero : ∀ i, (¬ ∃ j, e j=i) → x i=0) (r : ℕ) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
      trimmedSum (fun i => w i*x i) r = positiveCapacity (fun j => x (e j)) r := by
  obtain ⟨v,hv,hbudget,hvalue⟩ := positive_capacity_attained (fun j => x (e j)) hpos r
  let w := Function.extend e (fun j => v j/x (e j)) (fun _ => 0)
  have he (j : Fin p) : w (e j) = v j/x (e j) := e.injective.extend_apply _ _ j
  have hz (i : ι) (hi : ¬ ∃ j, e j=i) : w i=0 := Function.extend_apply' _ _ _ hi
  refine ⟨w,?_,?_,?_⟩
  · intro i
    by_cases hi : ∃ j, e j=i
    · obtain ⟨j,rfl⟩ := hi
      rw [he]
      exact div_nonneg (hv j) (hpos j).le
    · rw [hz i hi]
  · rw [sum_on_embedding e w hz]
    simpa only [he] using hbudget
  · rw [trimmedSum_restrict_support e _ (fun i hi => by simp [hzero i hi])]
    have hh (j : Fin p) : w (e j)*x (e j)=v j := by
      rw [he,div_mul_cancel₀ _ (hpos j).ne']
    simpa only [hh] using hvalue

theorem trimmedSum_nonneg (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (r : ℕ) :
    0 ≤ trimmedSum z r := by
  rw [trimmedSum_is_min]
  apply Finset.le_inf' (cardinalityAttacks_nonempty r)
  intro C _
  exact keptSum_nonneg _ _ C (fun _ => by norm_num) hz

theorem trimmedSum_positive_support (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (r : ℕ)
    (ht : 0 < trimmedSum z r) : r < (positiveSupport z).card := by
  by_contra hn
  have hc : positiveSupport z ∈ cardinalityAttacks r :=
    (mem_cardinalityAttacks r _).mpr (Nat.le_of_not_gt hn)
  have he : keptSum (fun _ => 1) z (positiveSupport z)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : 0 < z i
    · simp [positiveSupport,hi]
    · simp [positiveSupport,hi,le_antisymm (le_of_not_gt hi) (hz i)]
  have hb : trimmedSum z r ≤ 0 := by
    rw [trimmedSum_is_min]
    exact (Finset.inf'_le _ hc).trans_eq he
  linarith

def capacityValues (k l : ℕ) (x : ι → ℝ≥0) : Set ℝ :=
  {v | ∃ F : (ι → ℝ) → ℝ, (∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y) ∧
    ProbabilityRobustValid (cardinalityAttacks k) F ∧ v=worstValue F x l}

theorem capacity_upper {p : ℕ} [NeZero p] (e : Fin p ↪ ι) (x : ι → ℝ≥0)
    (hpos : ∀ j, 0 < (x (e j) : ℝ)) (hsort : Antitone (fun j => (x (e j) : ℝ)))
    (hzero : ∀ i, (¬ ∃ j, e j=i) → (x i : ℝ)=0) (k l : ℕ)
    (F : (ι → ℝ) → ℝ) (hFn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y)
    (hF : ProbabilityRobustValid (cardinalityAttacks k) F) :
    worstValue F x l ≤ max 1
      (positiveCapacity (fun j => (x (e j) : ℝ)) (min (Fintype.card ι) (k+l))) := by
  obtain ⟨a,w,ha,hw,hn,hdom⟩ := (complete_class_probability _ (cardinalityAttacks_nonempty k)
    F hFn).mp hF
  apply (worstValue_mono F _ hFn hdom x l).trans
  rw [robustAffine_worst_value k l a w hw x]
  have hb := nonnegative_capacity_upper e (fun i => (x i : ℝ)) w
    (fun i => (x i).coe_nonneg) hw hpos hsort hzero (min (Fintype.card ι) (k+l))
  have hs : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hc := positiveCapacity_nonneg (fun j => (x (e j) : ℝ)) hpos
    (min (Fintype.card ι) (k+l))
  have hma := le_max_left (1 : ℝ) (positiveCapacity (fun j => (x (e j) : ℝ))
    (min (Fintype.card ι) (k+l)))
  have hmc := le_max_right (1 : ℝ) (positiveCapacity (fun j => (x (e j) : ℝ))
    (min (Fintype.card ι) (k+l)))
  nlinarith [mul_le_mul_of_nonneg_right hmc hs,mul_le_mul_of_nonneg_right hma ha]

/-- The full minimax value, including normalized attaining rules and the intercept option. -/
theorem pointwise_capacity {p : ℕ} [NeZero p] (e : Fin p ↪ ι) (x : ι → ℝ≥0)
    (hpos : ∀ j, 0 < (x (e j) : ℝ)) (hsort : Antitone (fun j => (x (e j) : ℝ)))
    (hzero : ∀ i, (¬ ∃ j, e j=i) → (x i : ℝ)=0) (k l : ℕ) :
    IsGreatest (capacityValues k l x) (max 1
      (positiveCapacity (fun j => (x (e j) : ℝ)) (min (Fintype.card ι) (k+l)))) := by
  let r := min (Fintype.card ι) (k+l)
  let c := positiveCapacity (fun j => (x (e j) : ℝ)) r
  constructor
  · by_cases hc : c ≤ 1
    · have he : max 1 c=1 := max_eq_left hc
      refine ⟨fun _ => 1,fun _ _ => by norm_num,?_,?_⟩
      · apply (complete_class_probability _ (cardinalityAttacks_nonempty k) _
          (fun _ _ => by norm_num)).mpr
        refine ⟨1,fun _ => 0,by norm_num,fun _ => le_rfl,by simp,?_⟩
        intro y _
        simp [robustAffine,keptSum]
      · change max 1 c=worstValue (fun _ => 1) x l
        rw [he,worstValue_constant_one]
    · obtain ⟨w,hw,hs,hvalue⟩ := nonnegative_capacity_attained e (fun i => (x i : ℝ))
        (fun i => (x i).coe_nonneg) hpos hzero r
      refine ⟨fun y => robustAffine 0 w y (cardinalityAttacks k) (cardinalityAttacks_nonempty k),
        fun y hy => robustAffine_nonneg 0 w y _ _ le_rfl hw hy,
        affine_probability_valid k 0 w le_rfl hw (by simpa using hs),?_⟩
      rw [robustAffine_worst_value k l 0 w hw x,zero_add]
      change max 1 c=trimmedSum (fun i => w i*(x i : ℝ)) r
      rw [hvalue,max_eq_right (le_of_not_ge hc)]
  · rintro v ⟨F,hFn,hF,rfl⟩
    exact capacity_upper e x hpos hsort hzero k l F hFn hF

end
end EvidenceFusion
