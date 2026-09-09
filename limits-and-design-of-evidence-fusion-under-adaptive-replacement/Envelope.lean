import CorrectedProcess
import Mathlib.MeasureTheory.Measure.Dirac

open scoped BigOperators
open Finset Set MeasureTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section

def FiniteReplacements (x y : ℕ → ℝ) : Prop :=
  ∃ N, ∀ i, N ≤ i → x i = y i

def SparseReplacements (x y : ℕ → ℝ) : Prop :=
  Tendsto (fun n => (hamming (fun i : Fin n => x i) (fun i : Fin n => y i) : ℝ)/(n : ℝ))
    atTop (nhds 0)

theorem finite_replacement_count_bound (x y : ℕ → ℝ) (N : ℕ)
    (hN : ∀ i, N ≤ i → x i = y i) (n : ℕ) :
    hamming (fun i : Fin n => x i) (fun i : Fin n => y i) ≤ N := by
  let d := differences (fun i : Fin n => x i) (fun i : Fin n => y i)
  let e : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hs : d.map e ⊆ Finset.range N := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    apply Finset.mem_range.mpr
    by_contra hnot
    have he := hN j (Nat.le_of_not_gt hnot)
    simpa [d,differences,he] using hj
  have hc := Finset.card_le_card hs
  simpa [d,hamming] using hc

theorem finite_replacements_are_sparse (x y : ℕ → ℝ) (h : FiniteReplacements x y) :
    SparseReplacements x y := by
  obtain ⟨N,hN⟩ := h
  have hlim : Tendsto (fun n : ℕ => (N : ℝ)/(n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n)) _ hlim
  intro n
  exact div_le_div_of_nonneg_right (by exact_mod_cast finite_replacement_count_bound x y N hN n)
    (Nat.cast_nonneg n)

/-- Fixed-time validity under every conditional-mean null, on arbitrary
probability spaces and filtrations, for an indicated pathwise attack class. -/
def UniversalHistoryValid (P : (ℕ → ℝ) → (ℕ → ℝ) → Prop)
    (t : ℕ) (H : (Fin t → ℝ) → ℝ) : Prop :=
  ∀ (Ω : Type) [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) (X Y : ℕ → Ω → ℝ),
    (∀ i, StronglyMeasurable[ℱ (i+1)] (X i)) →
    (∀ i, StronglyMeasurable[m0] (Y i)) →
    (∀ i, Integrable (X i) μ) →
    (∀ i ω, 0 ≤ X i ω) → (∀ i ω, 0 ≤ Y i ω) →
    (∀ i, μ[X i|ℱ i] ≤ᵐ[μ] (1 : Ω → ℝ)) →
    (∀ᵐ ω ∂μ, P (fun i => X i ω) (fun i => Y i ω)) →
    AEStronglyMeasurable (fun ω => H (fun i => Y i ω)) μ →
    (∫ ω, H (fun i => Y i ω) ∂μ) ≤ 1

theorem zero_path_test (P : (ℕ → ℝ) → (ℕ → ℝ) → Prop) (t : ℕ)
    (H : (Fin t → ℝ) → ℝ) (hvalid : UniversalHistoryValid P t H)
    (y : ℕ → ℝ) (hy : ∀ i, 0 ≤ y i) (hP : P 0 y) :
    H (fun i => y i) ≤ 1 := by
  letI : MeasurableSpace Unit := ⊤
  let μ : Measure Unit := Measure.dirac ()
  let ℱ : Filtration ℕ (⊤ : MeasurableSpace Unit) := Filtration.const ℕ ⊤ le_rfl
  have hh := hvalid Unit μ ℱ (fun _ _ => 0) (fun i _ => y i)
    (fun _ => stronglyMeasurable_const) (fun _ => stronglyMeasurable_const)
    (fun _ => integrable_const (0 : ℝ)) (by simp) (fun i _ => hy i)
    (fun i => by
      change μ[(0 : Unit → ℝ)|ℱ i] ≤ᵐ[μ] (1 : Unit → ℝ)
      rw [condExp_zero]
      filter_upwards [] with ω
      norm_num) (Filter.Eventually.of_forall (fun _ => hP))
    stronglyMeasurable_const.aestronglyMeasurable
  simpa [μ] using hh

/-- Proposition S10 for arbitrary finite replacement counts. -/
theorem finite_envelope_necessity (t : ℕ) (H : (Fin t → ℝ) → ℝ)
    (hvalid : UniversalHistoryValid FiniteReplacements t H)
    (history : Fin t → ℝ) (hn : ∀ i, 0 ≤ history i) : H history ≤ 1 := by
  apply no_envelope_bound t H _ history hn
  intro y hy htail
  apply zero_path_test FiniteReplacements t H hvalid y hy
  obtain ⟨N,hN⟩ := htail
  exact ⟨N,fun i hi => (hN i hi).symm⟩

/-- Proposition S10 under only an unspecified vanishing replacement fraction. -/
theorem sparse_envelope_necessity (t : ℕ) (H : (Fin t → ℝ) → ℝ)
    (hvalid : UniversalHistoryValid SparseReplacements t H)
    (history : Fin t → ℝ) (hn : ∀ i, 0 ≤ history i) : H history ≤ 1 := by
  apply no_envelope_bound t H _ history hn
  intro y hy htail
  apply zero_path_test SparseReplacements t H hvalid y hy
  apply finite_replacements_are_sparse
  obtain ⟨N,hN⟩ := htail
  exact ⟨N,fun i hi => (hN i hi).symm⟩

end
end EvidenceFusion
