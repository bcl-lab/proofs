import ProbabilityReportingCore
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter Finset
open scoped BigOperators

namespace RepeatedEvidenceProbability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A real-valued e-value with its positivity and integrability requirements
explicit, on an arbitrary measure space. -/
structure IsEValue (μ : Measure Ω) (E : Ω → ℝ) : Prop where
  nonnegative : ∀ᵐ ω ∂μ, 0 ≤ E ω
  integrable : Integrable E μ
  mean_le_one : ∫ ω, E ω ∂μ ≤ 1

/-- Arbitrary measurable reporting dominated by one e-value is valid. -/
theorem IsEValue.of_dominated {E R : Ω → ℝ} (hE : IsEValue μ E)
    (hm : AEStronglyMeasurable R μ) (hn : ∀ᵐ ω ∂μ, 0 ≤ R ω)
    (hd : ∀ᵐ ω ∂μ, R ω ≤ E ω) : IsEValue μ R := by
  have hi : Integrable R μ := hE.integrable.mono' hm (by
    filter_upwards [hn,hd] with ω hn hd
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using hd)
  exact ⟨hn,hi,(integral_mono_ae hi hE.integrable hd).trans hE.mean_le_one⟩

/-- Normalizing a nonnegative integrable envelope by a positive upper bound on
its integral produces an e-value. -/
theorem normalized_isEValue (X : Ω → ℝ) (K : ℝ) (hK : 0 < K)
    (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hi : Integrable X μ) (hb : ∫ ω, X ω ∂μ ≤ K) :
    IsEValue μ (fun ω => X ω / K) := by
  refine ⟨?_, hi.div_const K, ?_⟩
  · filter_upwards [hn] with ω hω
    exact div_nonneg hω hK.le
  · rw [integral_div]
    exact (div_le_one hK).2 hb

/-- Fixed mixtures preserve e-values on arbitrary probability spaces, without
independence between their components. -/
theorem fixed_mixture_isEValue {J : Type*} [Fintype J] (E : J → Ω → ℝ) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1) (hE : ∀ j, IsEValue μ (E j)) :
    IsEValue μ (fun ω => ∑ j, w j * E j ω) := by
  have hi : ∀ j, Integrable (fun ω => w j * E j ω) μ :=
    fun j => (hE j).integrable.const_mul _
  refine ⟨?_,integrable_finset_sum _ (fun j _ => hi j), ?_⟩
  · have hn : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ E j ω := ae_all_iff.2 (fun j => (hE j).nonnegative)
    filter_upwards [hn] with ω hω
    exact sum_nonneg (fun j _ => mul_nonneg (hw j) (hω j))
  · rw [integral_finset_sum _ (fun j _ => hi j)]
    simp_rw [integral_const_mul]
    calc
      ∑ j, w j * ∫ ω, E j ω ∂μ ≤ ∑ j, w j * 1 :=
        sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hE j).mean_le_one (hw j))
      _ = 1 := by simpa using hs

/-- Expected false discovery proportion for any measurable self-consistent
selection, under arbitrary dependence between the tested e-values. -/
theorem self_consistent_false_discovery_rate {I : Type*} [Fintype I] [DecidableEq I]
    (H : Finset I) (R : Ω → Finset I) (E : I → Ω → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (hm : 0 < Fintype.card I)
    (hE : ∀ i ∈ H, IsEValue μ (E i))
    (hmeas : AEStronglyMeasurable (fun ω => falseDiscoveryProportion H (R ω)) μ)
    (hR : ∀ ω i, i ∈ R ω → (Fintype.card I : ℝ) ≤ α * (R ω).card * E i ω) :
    (∫ ω, falseDiscoveryProportion H (R ω) ∂μ) ≤ α * H.card / Fintype.card I := by
  let c : ℝ := α / Fintype.card I
  let G : Ω → ℝ := fun ω => c * ∑ i ∈ H, E i ω
  have hm' : (0:ℝ) < Fintype.card I := by exact_mod_cast hm
  have hc : 0 ≤ c := div_nonneg hα hm'.le
  have hGi : Integrable G μ := (integrable_finset_sum H (fun i hi => (hE i hi).integrable)).const_mul c
  have hpos : ∀ᵐ ω ∂μ, ∀ i ∈ H, 0 ≤ E i ω := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro hi
    exact (hE i hi).nonnegative
  have hbound : ∀ᵐ ω ∂μ, falseDiscoveryProportion H (R ω) ≤ G ω := by
    filter_upwards [hpos] with ω hω
    exact self_consistent_fdp_bound H (R ω) (fun i => E i ω) α hα hm hω (hR ω)
  have hnon : ∀ ω, 0 ≤ falseDiscoveryProportion H (R ω) := by
    intro ω
    unfold falseDiscoveryProportion
    positivity
  have hFi : Integrable (fun ω => falseDiscoveryProportion H (R ω)) μ := hGi.mono' hmeas (by
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hnon ω)] using hω)
  calc
    (∫ ω, falseDiscoveryProportion H (R ω) ∂μ) ≤ ∫ ω, G ω ∂μ := integral_mono_ae hFi hGi hbound
    _ = c * ∑ i ∈ H, ∫ ω, E i ω ∂μ := by
      rw [show G = (fun ω => c * ∑ i ∈ H, E i ω) from rfl, integral_const_mul,
        integral_finset_sum H (fun i hi => (hE i hi).integrable)]
    _ ≤ c * ∑ i ∈ H, (1:ℝ) := mul_le_mul_of_nonneg_left
      (sum_le_sum (fun i hi => (hE i hi).mean_le_one)) hc
    _ = α * H.card / Fintype.card I := by simp [c]; ring

theorem self_consistent_fdr_le_level {I : Type*} [Fintype I] [DecidableEq I]
    (H : Finset I) (R : Ω → Finset I) (E : I → Ω → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (hm : 0 < Fintype.card I)
    (hE : ∀ i ∈ H, IsEValue μ (E i))
    (hmeas : AEStronglyMeasurable (fun ω => falseDiscoveryProportion H (R ω)) μ)
    (hR : ∀ ω i, i ∈ R ω → (Fintype.card I : ℝ) ≤ α * (R ω).card * E i ω) :
    (∫ ω, falseDiscoveryProportion H (R ω) ∂μ) ≤ α := by
  have hm' : (0:ℝ) < Fintype.card I := by exact_mod_cast hm
  apply (self_consistent_false_discovery_rate H R E α hα hm hE hmeas hR).trans
  apply (div_le_iff₀ hm').2
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast H.card_le_univ) hα

/-- Expected false discovery rate for the explicitly defined step-up procedure.
The measurable-report condition is stated explicitly. -/
theorem eBH_false_discovery_rate {I : Type*} [Fintype I] [DecidableEq I]
    (H : Finset I) (E : I → Ω → ℝ) (α : ℝ)
    (hα : 0 ≤ α) (hm : 0 < Fintype.card I)
    (hE : ∀ i ∈ H, IsEValue μ (E i)) (hpos : ∀ i ω, 0 ≤ E i ω)
    (hmeas : AEStronglyMeasurable
      (fun ω => falseDiscoveryProportion H (eBHSelection (fun i => E i ω) α)) μ) :
    (∫ ω, falseDiscoveryProportion H (eBHSelection (fun i => E i ω) α) ∂μ) ≤ α := by
  exact self_consistent_fdr_le_level H (fun ω => eBHSelection (fun i => E i ω) α)
    E α hα hm hE hmeas (fun ω => eBH_self_consistent (fun i => E i ω) α hα (fun i => hpos i ω))

end RepeatedEvidenceProbability
