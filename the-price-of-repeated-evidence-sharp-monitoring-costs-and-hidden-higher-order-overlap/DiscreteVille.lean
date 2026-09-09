import TailCalibration
import Mathlib.Probability.Martingale.OptionalStopping

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace RepeatedEvidenceProbability

/-- Optional stopping yields the finite-horizon Ville bound for nonnegative
supermartingales. Only the initial expectation is bounded. -/
theorem ville_finite_horizon {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M ℱ μ)
    (h0 : ∀ n ω, 0 ≤ M n ω) (hinit : (∫ ω, M 0 ω ∂μ) ≤ 1)
    (u : ℝ) (hu : 0 < u) (N : ℕ) :
    μ {ω | ∃ n ≤ N, u ≤ M n ω} ≤ ENNReal.ofReal (1/u) := by
  let E : Set Ω := {ω | ∃ n ≤ N, u ≤ M n ω}
  let τ := hitting M (Ici u) 0 N
  have hτ : IsStoppingTime ℱ τ := hitting_isStoppingTime hM.adapted measurableSet_Ici
  have hb : ∀ ω, τ ω ≤ N := hitting_le
  have hs := hM.neg.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hτ
    (fun ω => Nat.zero_le (τ ω)) hb
  have hs' : (∫ ω, stoppedValue M τ ω ∂μ) ≤ ∫ ω, M 0 ω ∂μ := by
    simpa only [stoppedValue, Pi.neg_apply, integral_neg, neg_le_neg_iff] using hs
  have hE : MeasurableSet E := by
    have he : E = ⋃ n, ⋃ (_ : n ≤ N), {ω | u ≤ M n ω} := by
      ext ω
      simp [E]
    rw [he]
    exact MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun _ =>
      measurableSet_le measurable_const ((hM.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl)))
  have hi : Integrable (stoppedValue M τ) μ :=
    integrable_stoppedValue ℕ hτ hM.integrable hb
  have hpoint : ∀ ω, E.indicator (fun _ => u) ω ≤ stoppedValue M τ ω := by
    intro ω
    by_cases he : ω ∈ E
    · rw [indicator_of_mem he]
      obtain ⟨n,hn,hm⟩ := he
      exact stoppedValue_hitting_mem ⟨n,⟨Nat.zero_le n,hn⟩,hm⟩
    · rw [indicator_of_not_mem he]
      exact h0 _ ω
  have hbnd : μ.real E * u ≤ 1 := by
    calc
      μ.real E * u = ∫ ω, E.indicator (fun _ => u) ω ∂μ := by
        rw [integral_indicator hE,setIntegral_const,smul_eq_mul]
      _ ≤ ∫ ω, stoppedValue M τ ω ∂μ :=
        integral_mono ((integrable_const u).indicator hE) hi hpoint
      _ ≤ 1 := hs'.trans hinit
  change μ E ≤ _
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hu).2 hbnd)

/-- Ville's bound over an unbounded countable monitoring horizon. -/
theorem ville_countable_horizon {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M ℱ μ)
    (h0 : ∀ n ω, 0 ≤ M n ω) (hinit : (∫ ω, M 0 ω ∂μ) ≤ 1)
    (u : ℝ) (hu : 0 < u) :
    μ {ω | ∃ n, u ≤ M n ω} ≤ ENNReal.ofReal (1/u) := by
  have he : {ω | ∃ n, u ≤ M n ω} = ⋃ N : ℕ, {ω | ∃ n ≤ N, u ≤ M n ω} := by
    ext ω
    simp only [mem_setOf_eq,mem_iUnion]
    constructor
    · rintro ⟨n,hn⟩; exact ⟨n,n,le_rfl,hn⟩
    · rintro ⟨N,n,_,hn⟩; exact ⟨n,hn⟩
  have hm : Monotone (fun N : ℕ => {ω | ∃ n ≤ N, u ≤ M n ω}) := by
    intro j k hjk ω
    rintro ⟨n,hn,hnM⟩
    exact ⟨n,hn.trans hjk,hnM⟩
  rw [he, hm.measure_iUnion]
  exact iSup_le fun N => ville_finite_horizon μ ℱ M hM h0 hinit u hu N

/-- Tail bound for the extended-real running supremum. Using a strict tail
avoids pretending that an unattained supremum is a threshold crossing. -/
theorem ville_discrete_maximum_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (M : ℕ → Ω → ℝ) (hM : Supermartingale M ℱ μ)
    (h0 : ∀ n ω, 0 ≤ M n ω) (hinit : (∫ ω, M 0 ω ∂μ) ≤ 1)
    (u : ℝ) (hu : 0 < u) :
    μ {ω | ENNReal.ofReal u < ⨆ n, ENNReal.ofReal (M n ω)} ≤ ENNReal.ofReal (1/u) := by
  apply le_trans (measure_mono _) (ville_countable_horizon μ ℱ M hM h0 hinit u hu)
  intro ω hω
  change ENNReal.ofReal u < ⨆ n, ENNReal.ofReal (M n ω) at hω
  obtain ⟨n,hn⟩ := lt_iSup_iff.mp hω
  exact ⟨n,((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.le).1 hn).le⟩

end RepeatedEvidenceProbability
