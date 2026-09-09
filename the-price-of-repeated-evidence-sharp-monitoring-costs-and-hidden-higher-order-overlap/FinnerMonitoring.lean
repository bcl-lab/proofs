import FinnerSources
import CappedCost

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

/-- The full Finner upper bound for each admissible monitoring model. -/
theorem MonitoringModel.cost_le_finner {V I : Type} [Fintype V] [Fintype I]
    {A : V → I → Prop} [DecidableRel A] (model : MonitoringModel A)
    (a b : I → ℝ) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hb : ∀ v, (∑ i, if A v i then b i else 0) ≤ 1) :
    model.cost a ≤ ∏ i, (ENNReal.ofReal (1/(1-a i/b i))) ^ b i := by
  have hb0 : ∀ i, 0 < b i := fun i => (ha i).trans (hab i)
  have h := finner_sources model.μ model.sources model.sources_le model.independent
    A (fun i ω => model.maximum i ω ^ (a i/b i)) b
    (fun i => (model.maximum_source_measurable i).pow_const _)
    (fun i => (hb0 i).le) hb
  have he : ∀ i ω, (model.maximum i ω ^ (a i/b i)) ^ b i =
      model.maximum i ω ^ a i := by
    intro i ω
    rw [← ENNReal.rpow_mul,div_mul_cancel₀ _ (hb0 i).ne']
  simp_rw [he] at h
  apply h.trans
  apply Finset.prod_le_prod'
  intro i _
  apply ENNReal.rpow_le_rpow _ (hb0 i).le
  exact model.maximum_power_moment i _ (div_pos (ha i) (hb0 i))
    ((div_lt_one (hb0 i)).2 (hab i))

theorem universalCost_le_finner {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a b : I → ℝ)
    (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b i)
    (hb : ∀ v, (∑ i, if A v i then b i else 0) ≤ 1) :
    universalCost A a ≤ ∏ i, (ENNReal.ofReal (1/(1-a i/b i))) ^ b i := by
  exact iSup_le fun model => model.cost_le_finner a b ha hab hb

/-- Any strictly subunit common load bound yields a finite universal cost,
including networks whose total study power exceeds one. -/
theorem universalCost_le_load_bound {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (L : ℝ)
    (ha : ∀ i, 0 < a i) (hL0 : 0 < L) (hL1 : L < 1)
    (hload : ∀ v, sourceLoad A a v ≤ L) :
    universalCost A a ≤ ENNReal.ofReal ((1/(1-L)) ^ ((∑ i, a i)/L)) := by
  have hab : ∀ i, a i < a i/L := by
    intro i
    apply (lt_div_iff₀ hL0).2
    nlinarith [ha i]
  have hfeas : ∀ v, (∑ i, if A v i then a i/L else 0) ≤ 1 := by
    intro v
    have he : (∑ i, if A v i then a i/L else 0) = sourceLoad A a v / L := by
      simp only [sourceLoad,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
    rw [he]
    exact (div_le_one hL0).2 (hload v)
  have h := universalCost_le_finner A a (fun i => a i/L) ha hab hfeas
  have he : ∀ i, a i / (a i/L) = L := by
    intro i
    field_simp [(ha i).ne',hL0.ne']
  simp_rw [he] at h
  have hC : 0 < 1/(1-L) := one_div_pos.mpr (sub_pos.mpr hL1)
  simpa only [ENNReal.ofReal_rpow_of_pos hC,
    ← ENNReal.ofReal_prod_of_nonneg (fun _ _ => (Real.rpow_pos_of_pos hC _).le),
    ← Real.rpow_sum_of_pos hC, ← Finset.sum_div] using h

/-- Finner also supplies the full ceiling bound for a fractional matching;
the powers of the clipped maxima need not be below one. -/
theorem MonitoringModel.cappedCost_le_finner {V I : Type} [Fintype V] [Fintype I]
    {A : V → I → Prop} [DecidableRel A] (model : MonitoringModel A)
    (H : ℝ) (hH : 1 ≤ H) (a b : I → ℝ)
    (ha : ∀ i, 0 < a i) (hb0 : ∀ i, 0 < b i)
    (hb : ∀ v, (∑ i, if A v i then b i else 0) ≤ 1) :
    model.cappedCost H a ≤
      ∏ i, (ENNReal.ofReal (RepeatedEvidence.capMoment H (a i/b i))) ^ b i := by
  have h := finner_sources model.μ model.sources model.sources_le model.independent
    A (fun i ω => model.clippedMaximum H i ω ^ (a i/b i)) b
    (fun i => ((model.maximum_source_measurable i).min measurable_const).pow_const _)
    (fun i => (hb0 i).le) hb
  have he : ∀ i ω, (model.clippedMaximum H i ω ^ (a i/b i)) ^ b i =
      model.clippedMaximum H i ω ^ a i := by
    intro i ω
    rw [← ENNReal.rpow_mul,div_mul_cancel₀ _ (hb0 i).ne']
  simp_rw [he] at h
  apply h.trans
  apply Finset.prod_le_prod'
  intro i _
  exact ENNReal.rpow_le_rpow
    (model.clipped_power_moment i H _ hH (div_pos (ha i) (hb0 i))) (hb0 i).le

theorem universalCappedCost_le_finner {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (H : ℝ) (hH : 1 ≤ H) (a b : I → ℝ)
    (ha : ∀ i, 0 < a i) (hb0 : ∀ i, 0 < b i)
    (hb : ∀ v, (∑ i, if A v i then b i else 0) ≤ 1) :
    universalCappedCost A H a ≤
      ∏ i, (ENNReal.ofReal (RepeatedEvidence.capMoment H (a i/b i))) ^ b i := by
  exact iSup_le fun model => model.cappedCost_le_finner H hH a b ha hb0 hb

/-- Proposition 1, stated without a maximum operator: the actual universal
cost is finite exactly when every source load is strictly below one. -/
theorem universalCost_finite_iff {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (a : I → ℝ) (ha : ∀ i, 0 < a i) :
    universalCost A a ≠ ∞ ↔ ∀ v, sourceLoad A a v < 1 := by
  classical
  constructor
  · exact all_source_loads_lt_one_of_finite_cost A a
  · intro hload
    let s : Finset ℝ := insert 0 (Finset.univ.image (sourceLoad A a))
    have hs : s.Nonempty := ⟨0,Finset.mem_insert_self _ _⟩
    let L : ℝ := (s.max' hs + 1)/2
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
    have hle : ∀ v, sourceLoad A a v ≤ L := by
      intro v
      have hv : sourceLoad A a v ≤ s.max' hs := Finset.le_max' _ _
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩))
      dsimp [L]
      linarith
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (universalCost_le_load_bound A a L ha hL0 hL1 hle)

end RepeatedEvidenceProbability
