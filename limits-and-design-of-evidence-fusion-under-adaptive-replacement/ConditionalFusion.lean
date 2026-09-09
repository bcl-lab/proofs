import Sequential

open scoped BigOperators
open Finset MeasureTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι]

theorem conditional_affine_validity {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (F a : Ω → ℝ) (w X : ι → Ω → ℝ)
    (ham : StronglyMeasurable[m] a) (hwm : ∀ i, StronglyMeasurable[m] (w i))
    (han : ∀ ω, 0 ≤ a ω) (hwn : ∀ i ω, 0 ≤ w i ω)
    (hnorm : ∀ ω, a ω + ∑ i, w i ω = 1)
    (hXi : ∀ i, Integrable (X i) μ)
    (hc : ∀ i, μ[X i|m] ≤ᵐ[μ] (1 : Ω → ℝ))
    (hFm : AEStronglyMeasurable[m0] F μ) (hFn : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hdom : ∀ᵐ ω ∂μ, F ω ≤ a ω + ∑ i, w i ω*X i ω) :
    Integrable F μ ∧ μ[F|m] ≤ᵐ[μ] (1 : Ω → ℝ) := by
  have hab (ω : Ω) : a ω ≤ 1 := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ univ) => hwn i ω)
    linarith [hnorm ω]
  have hwb (i : ι) (ω : Ω) : w i ω ≤ 1 := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ univ) => hwn j ω) (Finset.mem_univ i)
    linarith [hnorm ω,han ω]
  have hai : Integrable a μ := by
    apply (integrable_const (1 : ℝ)).mono' (ham.mono hm |>.aestronglyMeasurable)
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs,abs_of_nonneg (han ω)] using hab ω
  have hwi (i : ι) : Integrable (fun ω => w i ω*X i ω) μ := by
    apply (hXi i).bdd_mul' (hwm i |>.mono hm |>.aestronglyMeasurable)
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs,abs_of_nonneg (hwn i ω)] using hwb i ω
  let G : Ω → ℝ := a + ∑ i, w i*X i
  have hsum : Integrable (∑ i, w i*X i) μ :=
    integrable_finset_sum' _ (fun i _ => hwi i)
  have hGi : Integrable G μ := hai.add hsum
  have hFi : Integrable F μ := by
    apply hGi.mono' hFm
    filter_upwards [hFn,hdom] with ω hn hd
    simpa [G,Finset.sum_apply,Real.norm_eq_abs,abs_of_nonneg hn] using hd
  have he := condExp_add hai hsum m
  have heSum := condExp_finset_sum (f := fun i => w i*X i)
    (fun i (_ : i ∈ univ) => hwi i) m
  have hp (i : ι) : μ[w i*X i|m] =ᵐ[μ] w i*μ[X i|m] :=
    condExp_mul_of_stronglyMeasurable_left (hwm i) (hwi i) (hXi i)
  have hpall := (ae_all_iff).mpr hp
  have hcall := (ae_all_iff).mpr hc
  have hGa : μ[a|m] = a := condExp_of_stronglyMeasurable hm ham hai
  have hGc : μ[G|m] ≤ᵐ[μ] (1 : Ω → ℝ) := by
    filter_upwards [he,heSum,hpall,hcall] with ω he heSum hp hc
    dsimp [G]
    rw [he]
    simp only [Pi.add_apply,hGa]
    rw [heSum]
    simp only [Finset.sum_apply]
    calc
      a ω + ∑ i, μ[w i*X i|m] ω = a ω + ∑ i, w i ω * μ[X i|m] ω := by
        simp_rw [hp]; rfl
      _ ≤ a ω + ∑ i, w i ω := by
        apply add_le_add_left
        apply Finset.sum_le_sum
        intro i _
        exact (mul_le_mul_of_nonneg_left (hc i) (hwn i ω)).trans_eq (mul_one _)
      _ = 1 := hnorm ω
  refine ⟨hFi,(condExp_mono hFi hGi ?_).trans hGc⟩
  filter_upwards [hdom] with ω hω
  simpa [G,Finset.sum_apply] using hω

theorem conditional_robust_fusion {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (S a : Ω → ℝ) (w X Y : ι → Ω → ℝ)
    (A : Finset (Finset ι)) (hA : A.Nonempty) (C : Ω → Finset ι)
    (ham : StronglyMeasurable[m] a) (hwm : ∀ i, StronglyMeasurable[m] (w i))
    (han : ∀ ω, 0 ≤ a ω) (hwn : ∀ i ω, 0 ≤ w i ω)
    (hnorm : ∀ ω, a ω + ∑ i, w i ω = 1)
    (hXi : ∀ i, Integrable (X i) μ) (hXn : ∀ᵐ ω ∂μ, ∀ i, 0 ≤ X i ω)
    (hc : ∀ i, μ[X i|m] ≤ᵐ[μ] (1 : Ω → ℝ))
    (hSm : AEStronglyMeasurable[m0] S μ) (hSn : ∀ᵐ ω ∂μ, 0 ≤ S ω)
    (hC : ∀ᵐ ω ∂μ, C ω ∈ A)
    (hclean : ∀ᵐ ω ∂μ, ∀ i, i ∉ C ω → Y i ω = X i ω)
    (hdom : ∀ᵐ ω ∂μ, S ω ≤ robustAffine (a ω) (fun i => w i ω)
      (fun i => Y i ω) A hA) :
    Integrable S μ ∧ μ[S|m] ≤ᵐ[μ] (1 : Ω → ℝ) := by
  apply conditional_affine_validity hm S a w X ham hwm han hwn hnorm hXi hc hSm hSn
  filter_upwards [hC,hclean,hdom,hXn] with ω hC he hd hx
  exact hd.trans (robustAffine_le_clean (a ω) (fun i => w i ω)
    (fun i => X i ω) (fun i => Y i ω) A hA (C ω) hC (fun i => hwn i ω) hx he)

end
end EvidenceFusion
