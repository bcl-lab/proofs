import FiniteRank
import Probability
import Mathlib.Data.Real.Archimedean

open scoped BigOperators
open Finset MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvidenceFusion
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def permuteScores (σ : Equiv.Perm ι) : (ι → ℝ) ≃ᵐ (ι → ℝ) where
  toFun x i := x (σ i)
  invFun x i := x (σ.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  measurable_toFun := measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))
  measurable_invFun := measurable_pi_lambda _ (fun i => measurable_pi_apply (σ.symm i))

def ExchangeableScoreLaw (μ : Measure (ι → ℝ)) : Prop :=
  ∀ σ : Equiv.Perm ι, MeasurePreserving (permuteScores σ) μ μ

theorem measurable_upperRank (i : ι) : Measurable (fun x : ι → ℝ => upperRank x i) := by
  have he : (fun x : ι → ℝ => upperRank x i) =
      fun x => ∑ j : ι, if x i ≤ x j then (1:ℕ) else 0 := by
    funext x
    simp [upperRank]
  rw [he]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_le (measurable_pi_apply i) (measurable_pi_apply j))
    measurable_const measurable_const

def rankEvent (q : ℕ) (i : ι) (x : ι → ℝ) : ℝ :=
  if upperRank x i ≤ q then 1 else 0

theorem measurable_rankEvent (q : ℕ) (i : ι) : Measurable (rankEvent q i) :=
  Measurable.ite (measurableSet_le (measurable_upperRank i) measurable_const)
    measurable_const measurable_const

theorem integrable_rankEvent (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (q : ℕ) (i : ι) : Integrable (rankEvent q i) μ := by
  apply (integrable_const (1:ℝ)).mono' (measurable_rankEvent q i).aestronglyMeasurable
  filter_upwards [] with x
  unfold rankEvent
  split_ifs <;> norm_num

def measureRankProbability (μ : Measure (ι → ℝ)) (q : ℕ) (i : ι) : ℝ :=
  ∫ x, rankEvent q i x ∂μ

theorem measure_rank_probability_equal (μ : Measure (ι → ℝ))
    (hex : ExchangeableScoreLaw μ) (q : ℕ) (i j : ι) :
    measureRankProbability μ q i = measureRankProbability μ q j := by
  unfold measureRankProbability
  calc
    _ = ∫ x, rankEvent q i (permuteScores (Equiv.swap i j) x) ∂μ :=
      ((hex (Equiv.swap i j)).integral_comp' (rankEvent q i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold rankEvent
      have hr : upperRank (permuteScores (Equiv.swap i j) x) i = upperRank x j := by
        change upperRank (fun k => x (Equiv.swap i j k)) i = _
        rw [upperRank_permutation]
        simp
      rw [hr]

/-- Conservative rank validity under any exchangeable Borel probability
law on a finite real score vector. There is no finite-support restriction. -/
theorem exchangeable_rank_bound (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (hex : ExchangeableScoreLaw μ) (q : ℕ) (i : ι) :
    measureRankProbability μ q i ≤ (q:ℝ)/Fintype.card ι := by
  have hcount : ∀ x : ι → ℝ, (∑ j, rankEvent q j x) ≤ q := by
    intro x
    have hc := rank_count_le x q
    have he : (∑ j, rankEvent q j x) =
        ((Finset.univ.filter fun j => upperRank x j ≤ q).card : ℝ) := by
      simp [rankEvent]
    rw [he]
    exact_mod_cast hc
  have hsum : ∑ j, measureRankProbability μ q j ≤ q := by
    unfold measureRankProbability
    rw [← integral_finset_sum Finset.univ (fun j _ => integrable_rankEvent μ q j)]
    calc
      _ ≤ ∫ _x : ι → ℝ, (q:ℝ) ∂μ := integral_mono
        (integrable_finset_sum Finset.univ (fun j _ => integrable_rankEvent μ q j))
        (integrable_const _) hcount
      _ = q := by simp
  have he : (∑ j, measureRankProbability μ q j) =
      (Fintype.card ι : ℝ)*measureRankProbability μ q i := by
    calc
      _ = ∑ _j : ι, measureRankProbability μ q i := by
        apply Finset.sum_congr rfl
        intro j _
        exact measure_rank_probability_equal μ hex q j i
      _ = _ := by simp
  rw [he] at hsum
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact (le_div_iff₀ hn).mpr (by nlinarith)

def attackedRank (T : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℕ :=
  1 + ((Finset.univ.erase i).filter fun j => T x ≤ x j).card

/-- Proposition S11 for general exchangeable real score laws. -/
theorem exchangeable_rank_evidence {L : Type*} [Fintype L]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (hex : ExchangeableScoreLaw μ) (v : L → ℝ) (q : L → ℕ) (i : ι)
    (hv : ∀ l, 0 ≤ v l) (hv1 : ∑ l, v l = 1) (hq : ∀ l, 0 < q l) :
    (∫ x, (∑ l, v l*((Fintype.card ι : ℝ)/q l)*rankEvent (q l) i x) ∂μ) ≤ 1 := by
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have ht : ∀ l, ((Fintype.card ι : ℝ)/q l)*measureRankProbability μ (q l) i ≤ 1 := by
    intro l
    have hql : (0:ℝ) < q l := by exact_mod_cast hq l
    have hh := mul_le_mul_of_nonneg_left (exchangeable_rank_bound μ hex (q l) i)
      (div_nonneg hn.le hql.le)
    have he : ((Fintype.card ι : ℝ)/q l)*((q l:ℝ)/Fintype.card ι) = 1 := by
      field_simp
    simpa [he] using hh
  rw [integral_finset_sum Finset.univ
    (fun l _ => (integrable_rankEvent μ (q l) i).const_mul (v l*((Fintype.card ι:ℝ)/q l)))]
  simp_rw [integral_const_mul]
  calc
    _ = ∑ l, v l*(((Fintype.card ι:ℝ)/q l)*measureRankProbability μ (q l) i) := by
      apply Finset.sum_congr rfl
      intro l _
      unfold measureRankProbability
      ring
    _ ≤ ∑ l, v l*1 := Finset.sum_le_sum fun l _ =>
      mul_le_mul_of_nonneg_left (ht l) (hv l)
    _ = 1 := by simpa using hv1

theorem attackedRank_ge_true (T : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ)
    (hT : T x ≤ x i) : upperRank x i ≤ attackedRank T i x := by
  have hself : i ∈ Finset.univ.filter (fun j => x i ≤ x j) := by simp
  have he : upperRank x i =
      1 + ((Finset.univ.erase i).filter fun j => x i ≤ x j).card := by
    unfold upperRank
    rw [← Finset.card_erase_add_one hself]
    rw [Finset.filter_erase]
    omega
  rw [he]
  unfold attackedRank
  apply Nat.add_le_add_left
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,
    hT.trans (Finset.mem_filter.mp hj).2⟩

/-- The rejection event in S14 is dominated by a conservative clean-rank
event. The proof allows arbitrary measurable, data-dependent attacked scores. -/
theorem robust_rank_calibration (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (hex : ExchangeableScoreLaw μ) (T : (ι → ℝ) → ℝ) (i : ι)
    (alpha : ℝ) (halpha : 0 ≤ alpha)
    (hT : ∀ᵐ x ∂μ, T x ≤ x i)
    (hmeas : AEStronglyMeasurable (fun x =>
      if (attackedRank T i x : ℝ)/Fintype.card ι ≤ alpha then (1:ℝ) else 0) μ) :
    (∫ x, (if (attackedRank T i x : ℝ)/Fintype.card ι ≤ alpha
      then (1:ℝ) else 0) ∂μ) ≤ alpha := by
  let q := Nat.floor (alpha*(Fintype.card ι : ℝ))
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have haq : 0 ≤ alpha*(Fintype.card ι : ℝ) := mul_nonneg halpha hn.le
  have hdom : ∀ᵐ x ∂μ,
      (if (attackedRank T i x : ℝ)/Fintype.card ι ≤ alpha then (1:ℝ) else 0)
      ≤ rankEvent q i x := by
    filter_upwards [hT] with x hx
    unfold rankEvent
    split_ifs with ha hr hr
    · exact le_rfl
    · have h1 : (attackedRank T i x : ℝ) ≤ alpha*Fintype.card ι :=
        (div_le_iff₀ hn).mp ha
      have h2 : attackedRank T i x ≤ q := (Nat.le_floor_iff haq).mpr h1
      exact False.elim (hr ((attackedRank_ge_true T i x hx).trans h2))
    · norm_num
    · exact le_rfl
  have hi : Integrable (fun x =>
      if (attackedRank T i x : ℝ)/Fintype.card ι ≤ alpha then (1:ℝ) else 0) μ := by
    apply (integrable_const (1:ℝ)).mono' hmeas
    filter_upwards [] with x
    split_ifs <;> norm_num
  calc
    _ ≤ measureRankProbability μ q i :=
      integral_mono_ae hi (integrable_rankEvent μ q i) hdom
    _ ≤ (q:ℝ)/Fintype.card ι := exchangeable_rank_bound μ hex q i
    _ ≤ alpha := (div_le_iff₀ hn).mpr (Nat.floor_le haq)

/-- Transfer the rank guarantee to an arbitrary probability space. The
attacker may use information and randomization beyond the clean scores. -/
theorem robust_rank_probability_general {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℝ)
    (hX : Measurable X) (hex : ExchangeableScoreLaw (μ.map X))
    (r : Ω → ℕ) (i : ι) (alpha : ℝ) (ha : 0 ≤ alpha)
    (hr : ∀ᵐ ω ∂μ, upperRank (X ω) i ≤ r ω)
    (hm : AEStronglyMeasurable (fun ω =>
      if (r ω:ℝ)/Fintype.card ι ≤ alpha then (1:ℝ) else 0) μ) :
    (∫ ω, (if (r ω:ℝ)/Fintype.card ι ≤ alpha then (1:ℝ) else 0) ∂μ) ≤ alpha := by
  letI : IsProbabilityMeasure (μ.map X) := MeasureTheory.isProbabilityMeasure_map hX.aemeasurable
  let q := Nat.floor (alpha*(Fintype.card ι:ℝ))
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have haq : 0 ≤ alpha*(Fintype.card ι:ℝ) := mul_nonneg ha hn.le
  have hdom : ∀ᵐ ω ∂μ,
      (if (r ω:ℝ)/Fintype.card ι ≤ alpha then (1:ℝ) else 0) ≤ rankEvent q i (X ω) := by
    filter_upwards [hr] with ω hω
    unfold rankEvent
    split_ifs with he he' he'
    · exact le_rfl
    · have hh : r ω ≤ q := (Nat.le_floor_iff haq).mpr ((div_le_iff₀ hn).mp he)
      exact False.elim (he' (hω.trans hh))
    · norm_num
    · exact le_rfl
  have hi : Integrable (fun ω =>
      if (r ω:ℝ)/Fintype.card ι ≤ alpha then (1:ℝ) else 0) μ := by
    apply (integrable_const (1:ℝ)).mono' hm
    filter_upwards [] with ω
    split_ifs <;> norm_num
  have hir : Integrable (fun ω => rankEvent q i (X ω)) μ :=
    (integrable_rankEvent (μ.map X) q i).comp_aemeasurable hX.aemeasurable
  calc
    _ ≤ ∫ ω, rankEvent q i (X ω) ∂μ := integral_mono_ae hi hir hdom
    _ = measureRankProbability (μ.map X) q i :=
      (integral_map hX.aemeasurable (measurable_rankEvent q i).aestronglyMeasurable).symm
    _ ≤ (q:ℝ)/Fintype.card ι := exchangeable_rank_bound (μ.map X) hex q i
    _ ≤ alpha := (div_le_iff₀ hn).mpr (Nat.floor_le haq)

/-- S14 with an arbitrary adaptive or randomized attacked scalar score on
the original probability space. X collects the clean upper-bound scores,
including the designated test score at i. -/
theorem calibration_with_adaptive_score {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ι → ℝ)
    (hX : Measurable X) (hex : ExchangeableScoreLaw (μ.map X))
    (T : Ω → ℝ) (i : ι) (alpha : ℝ) (ha : 0 ≤ alpha)
    (hT : ∀ᵐ ω ∂μ, T ω ≤ X ω i)
    (hm : AEStronglyMeasurable (fun ω =>
      if ((1 + ((Finset.univ.erase i).filter fun j => T ω ≤ X ω j).card : ℕ):ℝ)
        /Fintype.card ι ≤ alpha then (1:ℝ) else 0) μ) :
    (∫ ω, (if ((1 + ((Finset.univ.erase i).filter fun j => T ω ≤ X ω j).card : ℕ):ℝ)
      /Fintype.card ι ≤ alpha then (1:ℝ) else 0) ∂μ) ≤ alpha := by
  apply robust_rank_probability_general μ X hX hex _ i alpha ha _ hm
  filter_upwards [hT] with ω hω
  exact attackedRank_ge_true (fun _ => T ω) i (X ω) hω

end
end EvidenceFusion
