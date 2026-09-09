import MatchingRate
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.BorelCantelli

open scoped BigOperators NNReal ENNReal
open Set Finset MeasureTheory ProbabilityTheory Filter Function
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

theorem infinite_product_coordinate_law (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] (i : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ρ)).map (fun x : ℕ → ℝ≥0 => x i)=ρ := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]
  have he : (fun x : ℕ → ℝ≥0 => x i) ⁻¹' s = Set.pi ({i} : Finset ℕ) (fun _ => s) := by
    ext x; simp [Set.mem_pi]
  rw [he,Measure.infinitePi_pi _ (fun _ _ => hs)]
  simp

theorem infinite_product_independent (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] :
    iIndepFun (fun i (x : ℕ → ℝ≥0) => x i) (Measure.infinitePi (fun _ : ℕ => ρ)) := by
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S s hs
  have he : (⋂ i ∈ S, (fun x : ℕ → ℝ≥0 => x i) ⁻¹' s i)=Set.pi S s := by
    ext x; simp [Set.mem_pi]
  rw [he,Measure.infinitePi_pi _ hs]
  apply Finset.prod_congr rfl
  intro i hi
  have hh := congrArg (fun ν : Measure ℝ≥0 => ν (s i)) (infinite_product_coordinate_law ρ i)
  dsimp only at hh
  rw [Measure.map_apply (measurable_pi_apply i) (hs i hi)] at hh
  exact hh.symm

/-- The fixed-time consequence of universal conditional-null validity.
No attack is a member of every count-envelope attack model. -/
def ConditionalNullValid (A : ∀ n : ℕ, (Fin n → ℝ≥0) → ℝ) : Prop :=
  ∀ (Ω : Type) [m : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ≥0),
    (∀ i, StronglyMeasurable[ℱ (i+1)] (fun ω => (X i ω : ℝ))) →
    (∀ i, Integrable (fun ω => (X i ω : ℝ)) μ) →
    (∀ i, μ[(fun ω => (X i ω : ℝ))|ℱ i] ≤ᵐ[μ] (1 : Ω → ℝ)) →
      ∀ n, Integrable (fun ω => A n (fun i => X i ω)) μ ∧
        (∫ ω, A n (fun i => X i ω) ∂μ) ≤ 1

theorem conditional_null_implies_iid (A : ∀ n : ℕ, (Fin n → ℝ≥0) → ℝ)
    (hAm : ∀ n, Measurable (A n)) (hvalid : ConditionalNullValid A) : IIDNullValid A := by
  intro ρ hρ hi hmean n
  let μ := Measure.infinitePi (fun _ : ℕ => ρ)
  let Z := fun i (x : ℕ → ℝ≥0) => (x i : ℝ)
  let X := fun i (x : ℕ → ℝ≥0) => x (i+1)
  have hZm (i : ℕ) : StronglyMeasurable (Z i) := by
    exact (measurable_coe_nnreal_real.comp (measurable_pi_apply i)).stronglyMeasurable
  let ℱ := Filtration.natural Z hZm
  have hZi : iIndepFun Z μ := (infinite_product_independent ρ).comp
    (fun _ => fun x : ℝ≥0 => (x : ℝ)) (fun _ => measurable_coe_nnreal_real)
  have hid (i : ℕ) : IdentDistrib (fun x : ℕ → ℝ≥0 => x i) (fun x : ℝ≥0 => x) μ ρ :=
    ⟨(measurable_pi_apply i).aemeasurable,measurable_id.aemeasurable,
      by simpa using infinite_product_coordinate_law ρ i⟩
  have hreal (i : ℕ) := (hid i).comp measurable_coe_nnreal_real
  have hcal (i : ℕ) : μ[(fun ω => (X i ω : ℝ))|ℱ i] ≤ᵐ[μ] (1 : (ℕ → ℝ≥0) → ℝ) := by
    have hh := hZi.condExp_natural_ae_eq_of_lt hZm (Nat.lt_succ_self i)
    filter_upwards [hh] with ω hω
    change μ[Z (i+1)|ℱ i] ω ≤ 1
    rw [hω]
    exact (hreal (i+1)).integral_eq.trans_le hmean
  have hv := hvalid (ℕ → ℝ≥0) μ ℱ X
    (fun i => Filtration.adapted_natural hZm (i+1))
    (fun i => (hreal (i+1)).symm.integrable_snd hi) hcal n
  have hXm (i : ℕ) : Measurable (X i) := measurable_pi_apply (i+1)
  have hXi : iIndepFun X μ := (infinite_product_independent ρ).precomp
    (g := fun i => i+1) Nat.succ_injective
  have hmap (i : ℕ) : μ.map (X i)=ρ := infinite_product_coordinate_law ρ (i+1)
  have hH : Measurable (fun ω (i : Fin n) => X i ω) := measurable_pi_lambda _ (fun i => hXm i)
  have hhist := iid_history_law X hXm hXi ρ hmap n
  rw [← hhist]
  constructor
  · exact (integrable_map_measure (hAm n).aestronglyMeasurable hH.aemeasurable).mpr hv.1
  · rw [integral_map hH.aemeasurable (hAm n).aestronglyMeasurable]
    exact hv.2

end
end EvidenceFusion
