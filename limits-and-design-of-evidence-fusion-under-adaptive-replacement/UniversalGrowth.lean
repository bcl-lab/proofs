import DyadicSchedule

open scoped BigOperators NNReal ENNReal Topology
open Finset Set MeasureTheory ProbabilityTheory Filter Function
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section

def componentValue {n : ℕ} (j k : ℕ) (y : Fin n → ℝ) : ℝ :=
  robustProduct (fun i : Fin n => 1-delayFraction (2^j-1) (dyadicFraction j) i)
    (fun i : Fin n => delayFraction (2^j-1) (dyadicFraction j) i) y
    (cardinalityAttacks k) (cardinalityAttacks_nonempty k)

def universalValue {n : ℕ} (k : ℕ) (y : Fin n → ℝ) : ℝ :=
  1/2+(1/2)*∑ j ∈ Finset.range (activeCount n), delayedPrior j*componentValue j k y
    +1/(2*(activeCount n+1 : ℝ))

theorem componentValue_pos {n : ℕ} (j k : ℕ) (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) :
    0 < componentValue j k y := by
  apply robustProduct_positive _ _ _ _ _ _ _ hy
  · intro i
    unfold delayFraction
    split_ifs
    · exact sub_pos.mpr (dyadicFraction_mem j).2
    · norm_num
  · intro i
    unfold delayFraction
    split_ifs
    · exact (dyadicFraction_mem j).1.le
    · exact le_rfl

theorem universalValue_half {n : ℕ} (k : ℕ) (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i) :
    1/2 ≤ universalValue k y := by
  have hs : 0 ≤ ∑ j ∈ Finset.range (activeCount n), delayedPrior j*componentValue j k y :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (delayedPrior_pos j).le (componentValue_pos j k y hy).le)
  have ht : 0 ≤ 1/(2*(activeCount n+1 : ℝ)) := by positivity
  unfold universalValue
  linarith

theorem universalValue_component {n : ℕ} (j k : ℕ) (y : Fin n → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hj : j < activeCount n) :
    (delayedPrior j/2)*componentValue j k y ≤ universalValue k y := by
  have hs := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (activeCount n)) =>
      mul_nonneg (delayedPrior_pos i).le (componentValue_pos i k y hy).le)
    (Finset.mem_range.mpr hj)
  have ht : 0 ≤ 1/(2*(activeCount n+1 : ℝ)) := by positivity
  unfold universalValue
  nlinarith

variable {Ω : Type} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

def growthFunction (X : Ω → ℝ) (μ : Measure Ω) (u : ℝ) : ℝ :=
  ∫ ω, Real.log (1-u+u*X ω) ∂μ

theorem dyadic_growth_approximation (X : Ω → ℝ) (hXm : Measurable X)
    (hXn : ∀ ω, 0 ≤ X ω) (hint : Integrable (fun ω => Real.log (1+X ω)) μ)
    (u c : ℝ) (hu : u ∈ Set.Ioo 0 1) (hc : c < growthFunction X μ u) :
    ∃ j, c < growthFunction X μ (dyadicFraction j) := by
  let e := min u (1-u)/4
  have he : 0 < e := div_pos (lt_min hu.1 (by linarith [hu.2])) (by norm_num)
  have helu : 4*e ≤ u := by dsimp [e]; linarith [min_le_left u (1-u)]
  have heru : 4*e ≤ 1-u := by dsimp [e]; linarith [min_le_right u (1-u)]
  let delta := min e (e*(growthFunction X μ u-c)/2)
  have hd : 0 < delta := lt_min he (div_pos (mul_pos he (sub_pos.mpr hc)) (by norm_num))
  obtain ⟨j,hj⟩ := dyadicFraction_dense u delta hu hd
  have hje : |dyadicFraction j-u| < e := hj.trans_le (min_le_left _ _)
  have hjd : |dyadicFraction j-u| < e*(growthFunction X μ u-c)/2 :=
    hj.trans_le (min_le_right _ _)
  have hju := abs_lt.mp hje
  have hu' : u ∈ Set.Icc e (1-e) := ⟨by linarith,by linarith⟩
  have hj' : dyadicFraction j ∈ Set.Icc e (1-e) := ⟨by linarith,by linarith⟩
  have hb := expected_log_lipschitz X hXm hXn hint e u (dyadicFraction j) he hu' hj'
  change |growthFunction X μ (dyadicFraction j)-growthFunction X μ u| ≤ _ at hb
  have hm := mul_lt_mul_of_pos_left hjd (one_div_pos.mpr he)
  have heq : (1/e)*(e*(growthFunction X μ u-c)/2)=(growthFunction X μ u-c)/2 := by field_simp
  rw [heq] at hm
  refine ⟨j,?_⟩
  linarith [(abs_le.mp hb).1]

theorem growthFunction_bddAbove (X : Ω → ℝ) (hXm : Measurable X)
    (hXn : ∀ ω, 0 ≤ X ω) (hint : Integrable (fun ω => Real.log (1+X ω)) μ) :
    BddAbove ((growthFunction X μ) '' Set.Ico 0 1) := by
  refine ⟨∫ ω, Real.log (1+X ω) ∂μ,?_⟩
  rintro _ ⟨u,hu,rfl⟩
  apply integral_mono (log_factor_integrable X hXm hXn hint u hu.1 hu.2) hint
  intro ω
  apply Real.log_le_log
  · exact add_pos_of_pos_of_nonneg (sub_pos.mpr hu.2) (mul_nonneg hu.1 (hXn ω))
  · nlinarith [hu.1,mul_nonneg (sub_nonneg.mpr hu.2.le) (hXn ω)]

/-- The full uniform oracle lower rate for the explicit finite dyadic mixture,
expressed through every strict lower bound of the oracle supremum. -/
theorem computable_universal_growth (X : ℕ → Ω → ℝ)
    (hXm : ∀ i, Measurable (X i)) (hXn : ∀ i ω, 0 ≤ X i ω)
    (hint : Integrable (fun ω => Real.log (1+X 0 ω)) μ)
    (hindep : Pairwise ((IndepFun · · μ) on X))
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (k : ℕ → ℕ) (hk : Tendsto (fun n => (k n : ℝ)/(n : ℝ)) atTop (nhds 0)) :
    ∀ᵐ ω ∂μ, ∀ c : ℝ, c < sSup ((growthFunction (X 0) μ) '' Set.Ico 0 1) →
      ∀ᶠ n : ℕ in atTop, ∀ y : Fin n → ℝ, (∀ i, 0 ≤ y i) →
        hamming (fun i : Fin n => X i ω) y ≤ k n →
        c ≤ Real.log (universalValue (k n) y)/(n : ℝ) := by
  have hall := (ae_all_iff).mpr (fun j => delayed_fraction_growth_ae X hXm hXn hint
    hindep hident k hk (2^j-1) (dyadicFraction j)
    (dyadicFraction_mem j).1.le (dyadicFraction_mem j).2)
  filter_upwards [hall] with ω hω c hc
  obtain ⟨v,hv,hcv⟩ := (lt_csSup_iff (growthFunction_bddAbove (X 0) (hXm 0) (hXn 0) hint)
    (Set.Nonempty.image _ ⟨0,by norm_num⟩)).mp hc
  obtain ⟨u,hu,rfl⟩ := hv
  by_cases hu0 : u=0
  · have hc0 : c < 0 := by simpa [hu0,growthFunction] using hcv
    have hlim : Tendsto (fun n : ℕ => Real.log (1/2)/(n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [hlim.eventually (lt_mem_nhds hc0)] with n hn y hy _
    have hb := Real.log_le_log (by norm_num : (0 : ℝ) < 1/2) (universalValue_half (k n) y hy)
    exact hn.le.trans (div_le_div_of_nonneg_right hb (Nat.cast_nonneg n))
  · have hu' : u ∈ Set.Ioo 0 1 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩
    obtain ⟨j,hj⟩ := dyadic_growth_approximation (X 0) (hXm 0) (hXn 0) hint u c hu' hcv
    let d := (c+growthFunction (X 0) μ (dyadicFraction j))/2
    have hdc : c < d := by dsimp [d]; linarith
    have hdg : d < growthFunction (X 0) μ (dyadicFraction j) := by dsimp [d]; linarith
    have hlim : Tendsto (fun n : ℕ => Real.log (delayedPrior j/2)/(n : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hev := hlim.eventually (lt_mem_nhds (show c-d < 0 by linarith))
    filter_upwards [hω j d hdg,hev,activeCount_eventually j] with n hn hp hactive y hy ha
    have hcomp := hn y hy ha
    change d ≤ Real.log (componentValue j (k n) y)/(n : ℝ) at hcomp
    have hw : 0 < delayedPrior j/2 := div_pos (delayedPrior_pos j) (by norm_num)
    have hl := Real.log_le_log (mul_pos hw (componentValue_pos j (k n) y hy))
      (universalValue_component j (k n) y hy hactive)
    rw [Real.log_mul hw.ne' (componentValue_pos j (k n) y hy).ne'] at hl
    have hdiv := div_le_div_of_nonneg_right hl (Nat.cast_nonneg n)
    rw [add_div] at hdiv
    linarith

end
end EvidenceFusion
