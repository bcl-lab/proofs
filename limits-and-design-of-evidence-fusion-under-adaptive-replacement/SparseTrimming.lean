import LogLoss
import Mathlib.Probability.StrongLaw

open scoped BigOperators NNReal ENNReal Topology
open Finset Set MeasureTheory ProbabilityTheory Filter Function
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

def tailAbove (A : ℝ) (z : ℝ) : ℝ := if A < z then z else 0

theorem tailAbove_measurable (A : ℝ) : Measurable (tailAbove A) := by
  exact measurable_id.piecewise measurableSet_Ioi measurable_const

theorem tailAbove_integrable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (Z : Ω → ℝ) (hZi : Integrable Z μ) (hZm : Measurable Z) (A : ℝ) :
    Integrable (fun ω => tailAbove A (Z ω)) μ := by
  apply hZi.norm.mono' ((tailAbove_measurable A).comp hZm).aestronglyMeasurable
  filter_upwards [] with ω
  dsimp [tailAbove]
  split_ifs <;> simp

theorem tail_integral_tendsto_zero {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    (Z : Ω → ℝ) (hZi : Integrable Z μ) (hZm : Measurable Z) :
    Tendsto (fun n : ℕ => ∫ ω, tailAbove (n : ℝ) (Z ω) ∂μ) atTop (nhds 0) := by
  have hh := tendsto_integral_of_dominated_convergence (fun ω => ‖Z ω‖)
    (fun n : ℕ => ((tailAbove_measurable n).comp hZm).aestronglyMeasurable) hZi.norm
    (fun n => Filter.Eventually.of_forall (fun ω => show ‖tailAbove n (Z ω)‖ ≤ ‖Z ω‖ by
      dsimp [tailAbove]; split_ifs <;> simp))
    (show ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => tailAbove n (Z ω)) atTop (nhds (0 : ℝ)) from by
      filter_upwards [] with ω
      apply tendsto_const_nhds.congr'
      obtain ⟨N,hN⟩ := exists_nat_ge (Z ω)
      filter_upwards [eventually_ge_atTop N] with n hn
      have he : Z ω ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
      simp [tailAbove,not_lt.mpr he])
  simpa using hh

theorem largestSum_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (r : ℕ) : 0 ≤ largestSum z r := by
  have hh := Finset.le_sup' (fun C => ∑ i ∈ C, z i)
    ((mem_cardinalityAttacks r (∅ : Finset ι)).mpr (by simp))
  change 0 ≤ (cardinalityAttacks r).sup' (cardinalityAttacks_nonempty r) (fun C => ∑ i ∈ C, z i)
  simpa only [Finset.sum_empty] using hh

theorem largestSum_tail_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (z : ι → ℝ) (hz : ∀ i, 0 ≤ z i) (r : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    largestSum z r ≤ A*r + ∑ i, tailAbove A (z i) := by
  apply Finset.sup'_le (cardinalityAttacks_nonempty r)
  intro C hC
  have hh := sparse_trim_bound z C A hz hA
  have hcard : (C.card : ℝ) ≤ r := by exact_mod_cast (mem_cardinalityAttacks r C).mp hC
  have hc := mul_le_mul_of_nonneg_left hcard hA
  dsimp [tailAbove]
  linarith

/-- The integrable-tail trimming limit (S22), on one probability-one event.
The number removed may be any deterministic o(n) envelope. -/
theorem sparse_trimming_ae {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (Z : ℕ → Ω → ℝ)
    (hZi : Integrable (Z 0) μ) (hZm : ∀ i, Measurable (Z i))
    (hZn : ∀ i ω, 0 ≤ Z i ω)
    (hindep : Pairwise ((IndepFun · · μ) on Z))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) μ μ)
    (r : ℕ → ℕ) (hr : Tendsto (fun n => (r n : ℝ)/(n : ℝ)) atTop (nhds 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => largestSum (fun i : Fin n => Z i ω) (r n)/(n : ℝ))
      atTop (nhds 0) := by
  have hS (A : ℕ) : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, tailAbove A (Z i ω))/(n : ℝ))
        atTop (nhds (∫ ω, tailAbove A (Z 0 ω) ∂μ)) := by
    apply strong_law_ae_real (fun i ω => tailAbove A (Z i ω))
      (tailAbove_integrable (Z 0) hZi (hZm 0) A)
    · intro i j hij
      exact (hindep hij).comp (tailAbove_measurable A) (tailAbove_measurable A)
    · intro i
      exact (hident i).comp (tailAbove_measurable A)
  have hall := (ae_all_iff).mpr hS
  have htail := tail_integral_tendsto_zero (Z 0) hZi (hZm 0)
  filter_upwards [hall] with ω hω
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [] with n
    exact ha.trans_le (div_nonneg (largestSum_nonneg _ _) (Nat.cast_nonneg n))
  · intro b hb
    have hsmall := htail.eventually (gt_mem_nhds hb)
    obtain ⟨A,hA⟩ := hsmall.exists
    have hg := (hr.const_mul (A : ℝ)).add (hω A)
    simp only [mul_zero,zero_add] at hg
    have hge := hg.eventually (gt_mem_nhds hA)
    filter_upwards [hge] with n hn
    have hbound := largestSum_tail_bound (fun i : Fin n => Z i ω)
      (fun i => hZn i ω) (r n) (A : ℝ) (Nat.cast_nonneg A)
    have he := Fin.sum_univ_eq_sum_range (fun i => tailAbove A (Z i ω)) n
    rw [he] at hbound
    have hh := div_le_div_of_nonneg_right hbound (Nat.cast_nonneg n)
    have halgebra : ((A : ℝ)*(r n : ℝ) +
        ∑ i ∈ Finset.range n, tailAbove A (Z i ω))/(n : ℝ) =
        (A : ℝ)*((r n : ℝ)/(n : ℝ)) +
          (∑ i ∈ Finset.range n, tailAbove A (Z i ω))/(n : ℝ) := by ring
    rw [halgebra] at hh
    exact hh.trans_lt hn

end
end EvidenceFusion
