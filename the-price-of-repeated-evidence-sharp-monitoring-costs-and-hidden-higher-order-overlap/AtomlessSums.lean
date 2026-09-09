import IndependentCoordinates
import ExponentialSurvival

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem noAtoms_map_mul (ν : Measure ℝ) [NoAtoms ν] (c : ℝ) (hc : c ≠ 0) :
    NoAtoms (ν.map (fun x => c*x)) := by
  constructor
  intro a
  have hm : Measurable (fun x : ℝ => c*x) := measurable_const.mul measurable_id
  rw [Measure.map_apply hm (measurableSet_singleton a)]
  have he : (fun x : ℝ => c*x) ⁻¹' {a} = {a/c} := by
    ext x
    simp only [mem_preimage,mem_singleton_iff]
    constructor
    · intro h; apply (eq_div_iff hc).mpr; simpa only [mul_comm] using h
    · intro h; rw [h]; field_simp
  rw [he]
  exact measure_singleton _

theorem independent_sum_noAtoms {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hi : IndepFun X Y μ) [NoAtoms (μ.map Y)] : NoAtoms (μ.map (fun ω => X ω + Y ω)) := by
  haveI : IsProbabilityMeasure (μ.map X) := isProbabilityMeasure_map hX.aemeasurable
  haveI : IsProbabilityMeasure (μ.map Y) := isProbabilityMeasure_map hY.aemeasurable
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hi
  constructor
  intro a
  have hm : MeasurableSet {p : ℝ × ℝ | p.1+p.2=a} :=
    measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const
  calc
    _ = (μ.map (fun ω => (X ω,Y ω))) {p : ℝ × ℝ | p.1+p.2=a} := by
      rw [Measure.map_apply (hX.add hY) (measurableSet_singleton a),
        Measure.map_apply (hX.prodMk hY) hm]
      rfl
    _ = ((μ.map X).prod (μ.map Y)) {p : ℝ × ℝ | p.1+p.2=a} := by rw [hmap]
    _ = ∫⁻ x, (μ.map Y) {y : ℝ | x+y=a} ∂μ.map X := by
      rw [Measure.prod_apply hm]
      rfl
    _ = 0 := by
      have hz : ∀ x : ℝ, (μ.map Y) {y : ℝ | x+y=a} = 0 := by
        intro x
        have he : {y : ℝ | x+y=a} = {a-x} := by
          ext y
          simp only [mem_setOf_eq,mem_singleton_iff]
          constructor <;> intro h <;> linarith
        rw [he]
        exact measure_singleton _
      simp only [hz,lintegral_zero]

theorem independent_finite_sum_noAtoms {J Ω : Type} [Fintype J] [DecidableEq J]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : J → Ω → ℝ) (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (j : J) [NoAtoms (μ.map (X j))] :
    NoAtoms (μ.map (fun ω => ∑ i, X i ω)) := by
  let Y : Ω → ℝ := fun ω => ∑ i ∈ Finset.univ.erase j, X i ω
  have hY : Measurable Y := Finset.measurable_sum _ (fun i _ => hX i)
  have hInd : IndepFun Y (X j) μ := by
    have h := hi.indepFun_finset_sum_of_not_mem hX (Finset.not_mem_erase j Finset.univ)
    convert h using 1
    ext ω
    simp [Y]
  have he : (fun ω => ∑ i, X i ω) = (fun ω => Y ω + X j ω) := by
    funext ω
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
  rw [he]
  exact independent_sum_noAtoms μ Y (X j) hY (hX j) hInd

end RepeatedEvidenceProbability
