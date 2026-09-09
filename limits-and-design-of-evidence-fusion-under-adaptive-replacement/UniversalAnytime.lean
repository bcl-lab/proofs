import UniversalGrowth

open scoped BigOperators NNReal ENNReal
open Finset Set MeasureTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m}

def universalProcess (Y : ℕ → Ω → ℝ) (k : ℕ → ℕ) (n : ℕ) (ω : Ω) : ℝ :=
  universalValue (k n) (fun i : Fin n => Y i ω)

theorem delayed_fraction_bounds (j i : ℕ) :
    0 ≤ delayFraction (2^j-1) (dyadicFraction j) i ∧
      delayFraction (2^j-1) (dyadicFraction j) i ≤ 1 := by
  unfold delayFraction
  split_ifs
  · exact ⟨(dyadicFraction_mem j).1.le,(dyadicFraction_mem j).2.le⟩
  · constructor <;> norm_num

theorem inactive_clean_component (X : ℕ → Ω → ℝ) (n j : ℕ) (hj : activeCount n ≤ j) :
    productProcess (fun i ω => 1-delayFraction (2^j-1) (dyadicFraction j) i+
      delayFraction (2^j-1) (dyadicFraction j) i*X i ω) n = 1 := by
  have hnj : n < 2^j := Nat.lt_of_not_ge (by
    intro h; exact (Nat.not_lt.mpr hj) ((activeCount_characterization n j).mpr h))
  funext ω
  apply Finset.prod_eq_one
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hs : ¬ 2^j-1 ≤ i := by omega
  simp [delayFraction,hs]

theorem delayedMixture_measurable (E : ℕ → ℕ → Ω → ℝ) (J : ℕ → ℕ)
    (hE : ∀ j n, StronglyMeasurable[m] (E j n)) (n : ℕ) :
    StronglyMeasurable[m] (delayedMixture E J n) := by
  have hs : StronglyMeasurable[m]
      (fun ω => ∑ j ∈ Finset.range (J n), delayedPrior j*E j n ω) := by
    apply Finset.stronglyMeasurable_sum
    intro j _
    exact stronglyMeasurable_const.mul (hE j n)
  exact (stronglyMeasurable_const.add (stronglyMeasurable_const.mul hs)).add stronglyMeasurable_const

/-- Anytime validity of the exact finite implementation in S17, including its activation schedule. -/
theorem computable_universal_anytime (X Y : ℕ → Ω → ℝ) (k : ℕ → ℕ)
    (hXm : ∀ i, StronglyMeasurable[ℱ (i+1)] (X i))
    (hYm : ∀ i, StronglyMeasurable[m] (Y i))
    (hXi : ∀ i, Integrable (X i) μ) (hXn : ∀ i ω, 0 ≤ X i ω)
    (hYn : ∀ i ω, 0 ≤ Y i ω)
    (hc : ∀ i, μ[X i|ℱ i] ≤ᵐ[μ] (1 : Ω → ℝ))
    (hattack : ∀ n, ∀ᵐ ω ∂μ,
      hamming (fun i : Fin n => X i ω) (fun i : Fin n => Y i ω) ≤ k n) :
    AnytimeValid (universalProcess Y k) ℱ μ := by
  let lam := fun j i (_ : Ω) => delayFraction (2^j-1) (dyadicFraction j) i
  let M := fun j => productProcess (fun i ω => 1-lam j i ω+lam j i ω*X i ω)
  let R := fun j => correctedProcess (lam j) Y k
  have hlm (j i : ℕ) : StronglyMeasurable[ℱ i] (lam j i) := stronglyMeasurable_const
  have hln (j i : ℕ) (ω : Ω) : 0 ≤ lam j i ω := (delayed_fraction_bounds j i).1
  have hl1 (j i : ℕ) (ω : Ω) : lam j i ω ≤ 1 := (delayed_fraction_bounds j i).2
  have hM (j : ℕ) : Supermartingale (M j) ℱ μ :=
    clean_betting_supermartingale (lam j) X (hlm j) hXm (hln j) (hl1 j) hXi hXn hc
  have hMn (j n : ℕ) (ω : Ω) : 0 ≤ M j n ω := productProcess_nonneg _
    (fun i ω => add_nonneg (sub_nonneg.mpr (hl1 j i ω)) (mul_nonneg (hln j i ω) (hXn i ω))) n ω
  have hInactive (n j : ℕ) (hj : activeCount n ≤ j) : M j n=1 :=
    inactive_clean_component X n j hj
  have hMix := delayedMixture_supermartingale M activeCount hM activeCount_monotone hInactive
  have hMix0 := delayedMixture_zero M activeCount activeCount_zero
  have hMixn := delayedMixture_nonneg M activeCount hMn
  have hdom (j n : ℕ) : R j n ≤ᵐ[μ] M j n :=
    correctedProcess_domination (lam j) X Y k (hln j) (hl1 j) hXn hattack n
  have hRmeas (j n : ℕ) : StronglyMeasurable[m] (R j n) :=
    correctedProcess_measurable (lam j) Y k (fun _ => stronglyMeasurable_const) hYm n
  have hRn (j n : ℕ) (ω : Ω) : 0 ≤ R j n ω :=
    correctedProcess_nonneg (lam j) Y k (hln j) (hl1 j) hYn n ω
  have he : universalProcess Y k=delayedMixture R activeCount := rfl
  rw [he]
  constructor
  · intro τ hτ N hN
    exact dominated_bounded_stopping hMix hMix0
      (fun n => (delayedMixture_measurable R activeCount hRmeas n).aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (delayedMixture_nonneg R activeCount hRn n))
      (delayedMixture_domination M R activeCount hdom) τ hτ N hN
  · intro a ha
    apply le_trans _ (ville_supremum hMix hMix0 hMixn a ha)
    apply measure_mono_ae
    have hall := (ae_all_iff).mpr (delayedMixture_domination M R activeCount hdom)
    filter_upwards [hall] with ω hω
    intro hsup
    exact hsup.trans (iSup_mono (fun n => ENNReal.ofReal_le_ofReal (hω n)))

end
end EvidenceFusion
