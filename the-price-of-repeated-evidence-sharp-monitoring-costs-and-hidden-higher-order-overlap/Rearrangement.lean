import ProductLayerCake

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace RepeatedEvidenceProbability

/-- Upper level sets of two increasing functions on a line are nested. -/
theorem monotone_level_sets_nested {f g : ℝ → ℝ} {D : Set ℝ}
    (hf : MonotoneOn f D) (hg : MonotoneOn g D) (s t : ℝ) :
    (D ∩ {u | s < f u}) ⊆ {u | t < g u} ∨
      (D ∩ {u | t < g u}) ⊆ {u | s < f u} := by
  classical
  by_cases h : (D ∩ {u | s < f u}) ⊆ {u | t < g u}
  · exact Or.inl h
  · right
    obtain ⟨u,⟨huD,hus⟩,hut⟩ := Set.not_subset.mp h
    intro v hv
    have huv : u < v := by
      by_contra h'
      have := hg hv.1 huD (le_of_not_gt h')
      exact hut (hv.2.trans_le this)
    exact hus.trans_le (hf huD hv.1 huv.le)

theorem uniformRank_joint_tail {F G : ℝ → ℝ}
    (hF : MonotoneOn F (Ioo (0:ℝ) 1)) (hG : MonotoneOn G (Ioo (0:ℝ) 1))
    (s t : ℝ) :
    uniformRank {u | s < F u ∧ t < G u} =
      min (uniformRank {u | s < F u}) (uniformRank {u | t < G u}) := by
  rcases monotone_level_sets_nested hF hG s t with h | h
  · have he : {u | s < F u ∧ t < G u} =ᵐ[uniformRank] {u | s < F u} := by
      filter_upwards [uniformRank_open] with u hu
      exact propext ⟨And.left,fun hs => ⟨hs,h ⟨hu,hs⟩⟩⟩
    have hle : uniformRank {u | s < F u} ≤ uniformRank {u | t < G u} := by
      apply measure_mono_ae
      filter_upwards [uniformRank_open] with u hu
      exact fun hs => h ⟨hu,hs⟩
    rw [measure_congr he,min_eq_left hle]
  · have he : {u | s < F u ∧ t < G u} =ᵐ[uniformRank] {u | t < G u} := by
      filter_upwards [uniformRank_open] with u hu
      exact propext ⟨And.right,fun ht => ⟨h ⟨hu,ht⟩,ht⟩⟩
    have hle : uniformRank {u | t < G u} ≤ uniformRank {u | s < F u} := by
      apply measure_mono_ae
      filter_upwards [uniformRank_open] with u hu
      exact fun ht => h ⟨hu,ht⟩
    rw [measure_congr he,min_eq_right hle]

/-- Rearrangement upper bound under marginal tail domination. No finiteness
of the product expectation is assumed. -/
theorem comonotone_product_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (f g : Ω → ℝ) (F G : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hF : Measurable F) (hG : Measurable G)
    (hmF : MonotoneOn F (Ioo (0:ℝ) 1)) (hmG : MonotoneOn G (Ioo (0:ℝ) 1))
    (htF : ∀ s > 0, μ {x | s < f x} ≤ uniformRank {u | s < F u})
    (htG : ∀ t > 0, μ {x | t < g x} ≤ uniformRank {u | t < G u}) :
    (∫⁻ x, ENNReal.ofReal (f x) * ENNReal.ofReal (g x) ∂μ) ≤
      ∫⁻ u, ENNReal.ofReal (F u) * ENNReal.ofReal (G u) ∂uniformRank := by
  rw [product_layercake μ f g hf hg,product_layercake uniformRank F G hF hG]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [uniformRank_joint_tail hmF hmG]
  apply le_min
  · exact (measure_mono (fun _ h => h.1)).trans (htF s hs)
  · exact (measure_mono (fun _ h => h.2)).trans (htG t ht)

end RepeatedEvidenceProbability
