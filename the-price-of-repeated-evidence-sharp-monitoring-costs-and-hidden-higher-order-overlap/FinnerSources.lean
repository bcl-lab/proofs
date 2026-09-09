import FinnerProduct
import StochasticModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace RepeatedEvidenceProbability

/-- A copy of the sample space carrying exactly one source's information. -/
structure SourcePoint (Ω : Type) (m : MeasurableSpace Ω) where
  value : Ω

instance SourcePoint.measurableSpace (Ω : Type) (m : MeasurableSpace Ω) :
    MeasurableSpace (SourcePoint Ω m) := m.comap SourcePoint.value

instance SourcePoint.nonempty (Ω : Type) [Nonempty Ω] (m : MeasurableSpace Ω) :
    Nonempty (SourcePoint Ω m) := ⟨⟨Classical.arbitrary Ω⟩⟩

theorem sourcePoint_measurable {Ω : Type} [mΩ : MeasurableSpace Ω]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ) :
    @Measurable Ω (SourcePoint Ω m) mΩ _ (fun ω => ⟨ω⟩) := by
  rw [measurable_iff_comap_le]
  change (m.comap SourcePoint.value).comap (fun ω => ⟨ω⟩) ≤ mΩ
  rw [MeasurableSpace.comap_comp]
  change m.comap id ≤ mΩ
  simpa only [MeasurableSpace.comap_id] using hm

/-- Doob-Dynkin turns study-source measurability into an actual coordinate
function; no regularity of the primitive source value spaces is required. -/
theorem study_measurable_factor {V I Ω : Type}
    (A : V → I → Prop) (sources : V → MeasurableSpace Ω) (i : I)
    (f : Ω → ℝ≥0∞) (hf : Measurable[studyInformation A sources i] f) :
    ∃ g : (∀ v, SourcePoint Ω (sources v)) → ℝ≥0∞,
      Measurable g ∧
      (∀ ω, f ω = g (fun _ => ⟨ω⟩)) ∧
      (∀ x y, (∀ v, A v i → x v = y v) → g x = g y) := by
  let D : Ω → (∀ v : {v // A v i}, SourcePoint Ω (sources v)) :=
    fun ω _ => ⟨ω⟩
  have he : (MeasurableSpace.pi.comap D) = studyInformation A sources i := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      SourcePoint.measurableSpace, MeasurableSpace.comap_comp]
    change (⨆ v : {v // A v i}, (sources v).comap id) = _
    simp only [MeasurableSpace.comap_id, iSup_subtype, studyInformation]
  rw [← he] at hf
  obtain ⟨h,hh,heq⟩ := hf.exists_eq_measurable_comp
  refine ⟨fun x => h (fun v => x v.val), ?_, ?_, ?_⟩
  · exact hh.comp (measurable_pi_iff.mpr (fun v => measurable_pi_apply v.val))
  · intro ω
    exact congrFun heq ω
  · intro x y hxy
    apply congrArg h
    funext v
    exact hxy v.val v.property

/-- General Finner inequality on an ambient probability space with mutually
independent source sigma-algebras. The passage to a product law is proved. -/
theorem finner_sources {V I Ω : Type} [Fintype V] [Fintype I]
    [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sources : V → MeasurableSpace Ω) (hsub : ∀ v, sources v ≤ mΩ)
    (hind : iIndep sources μ) (A : V → I → Prop) [DecidableRel A]
    (f : I → Ω → ℝ≥0∞) (p : I → ℝ)
    (hf : ∀ i, Measurable[studyInformation A sources i] (f i))
    (hp : ∀ i, 0 ≤ p i)
    (hload : ∀ v, (∑ i, if A v i then p i else 0) ≤ 1) :
    (∫⁻ ω, ∏ i, f i ω ^ p i ∂μ) ≤ ∏ i, (∫⁻ ω, f i ω ∂μ) ^ p i := by
  classical
  haveI : Nonempty Ω := (nonempty_of_measure_ne_zero (by simp : μ univ ≠ 0)).to_subtype
    |>.map Subtype.val
  let X (v : V) := SourcePoint Ω (sources v)
  let Z (v : V) (ω : Ω) : X v := ⟨ω⟩
  have hZ : ∀ v, Measurable (Z v) := fun v => sourcePoint_measurable _ (hsub v)
  have hiZ : iIndepFun Z μ := by
    rw [iIndepFun_iff_iIndep]
    simp only [X,SourcePoint.measurableSpace,MeasurableSpace.comap_comp]
    change iIndep (fun v => (sources v).comap id) μ
    simpa only [MeasurableSpace.comap_id] using hind
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map (fun v => (hZ v).aemeasurable)).mp hiZ
  choose g hg heq hdep using fun i => study_measurable_factor A sources i (f i) (hf i)
  haveI : ∀ v, IsProbabilityMeasure (μ.map (Z v)) := fun v =>
    isProbabilityMeasure_map (hZ v).aemeasurable
  have h := finner_product (fun v => μ.map (Z v)) A g p hg hp hload hdep
  simp_rw [← hmap] at h
  rw [lintegral_map
    (Finset.univ.measurable_prod (fun i _ => (hg i).pow_const _))
    (measurable_pi_iff.mpr hZ)] at h
  have hint (i : I) : (∫⁻ x, g i x ∂μ.map (fun ω v => Z v ω)) =
      ∫⁻ ω, f i ω ∂μ := by
    rw [lintegral_map (hg i) (measurable_pi_iff.mpr hZ)]
    simp only [Z, ← heq]
  simp_rw [hint] at h
  simpa only [Z, ← heq] using h

end RepeatedEvidenceProbability
