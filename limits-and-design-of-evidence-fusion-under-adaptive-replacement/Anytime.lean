import Sequential

open scoped BigOperators NNReal ENNReal
open Finset Set MeasureTheory Filter
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EvidenceFusion
noncomputable section
variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}

theorem ville_finite {M : ℕ → Ω → ℝ} (hM : Supermartingale M ℱ μ)
    (hzero : M 0 = 1) (hn : ∀ n ω, 0 ≤ M n ω) (a : ℝ) (ha : 0 < a) (N : ℕ) :
    μ {ω | ∃ n ≤ N, a ≤ M n ω} ≤ ENNReal.ofReal (1/a) := by
  let τ := hitting M (Set.Ici a) 0 N
  have hτ : IsStoppingTime ℱ τ := hitting_isStoppingTime hM.adapted measurableSet_Ici
  obtain ⟨hi,he⟩ := supermartingale_bounded_stopping hM hzero τ hτ N hitting_le
  have hs : {ω | ∃ n ≤ N, a ≤ M n ω} ⊆ {ω | a ≤ stoppedValue M τ ω} := by
    rintro ω ⟨n,hnN,hnM⟩
    exact stoppedValue_hitting_mem ⟨n,⟨Nat.zero_le _,hnN⟩,hnM⟩
  apply (measure_mono hs).trans
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => hn (τ ω) ω)) hi a
  change a * μ.real {ω | a ≤ stoppedValue M τ ω} ≤
    ∫ ω, stoppedValue M τ ω ∂μ at hm
  have hb : μ.real {ω | a ≤ stoppedValue M τ ω} ≤ 1/a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ {ω | a ≤ stoppedValue M τ ω})]
  exact ENNReal.ofReal_le_ofReal hb

theorem ville_crossing {M : ℕ → Ω → ℝ} (hM : Supermartingale M ℱ μ)
    (hzero : M 0 = 1) (hn : ∀ n ω, 0 ≤ M n ω) (a : ℝ) (ha : 0 < a) :
    μ {ω | ∃ n, a ≤ M n ω} ≤ ENNReal.ofReal (1/a) := by
  let E : ℕ → Set Ω := fun N => {ω | ∃ n ≤ N, a ≤ M n ω}
  have hE : Monotone E := by
    intro N K hNK ω hω
    obtain ⟨n,hnN,haM⟩ := hω
    exact ⟨n,hnN.trans hNK,haM⟩
  have heq : {ω | ∃ n, a ≤ M n ω} = ⋃ N, E N := by
    ext ω
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,E]
    constructor
    · rintro ⟨n,h⟩; exact ⟨n,n,le_rfl,h⟩
    · rintro ⟨N,n,_,h⟩; exact ⟨n,h⟩
  rw [heq,hE.measure_iUnion]
  exact iSup_le fun N => ville_finite hM hzero hn a ha N

/-- Ville's inequality includes supremum values approached without being
attained at a finite time. The extended nonnegative supremum allows divergence. -/
theorem ville_supremum {M : ℕ → Ω → ℝ} (hM : Supermartingale M ℱ μ)
    (hzero : M 0 = 1) (hn : ∀ n ω, 0 ≤ M n ω) (a : ℝ) (ha : 0 < a) :
    μ {ω | ENNReal.ofReal a ≤ ⨆ n, ENNReal.ofReal (M n ω)} ≤ ENNReal.ofReal (1/a) := by
  let E : Set Ω := {ω | ENNReal.ofReal a ≤ ⨆ n, ENNReal.ofReal (M n ω)}
  let p : ℝ := μ.real E
  have hbound (c : ℝ) (hc : 0 < c) (hca : c < a) : p ≤ 1/c := by
    have hs : E ⊆ {ω | ∃ n, c ≤ M n ω} := by
      intro ω hω
      have hh : ENNReal.ofReal c < ⨆ n, ENNReal.ofReal (M n ω) :=
        (ENNReal.ofReal_lt_ofReal_iff ha).mpr hca |>.trans_le hω
      obtain ⟨n,hnc⟩ := lt_iSup_iff.mp hh
      refine ⟨n,?_⟩
      by_contra hnot
      have hh' := ENNReal.ofReal_le_ofReal (le_of_not_ge hnot)
      exact (not_lt_of_ge hh') hnc
    have hh := (measure_mono hs).trans (ville_crossing hM hzero hn c hc)
    have he := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/c)] at he
    exact he
  have hp : p ≤ 1/a := by
    by_contra hnot
    have hpa : 1/a < p := lt_of_not_ge hnot
    have hpp : 0 < p := (one_div_pos.mpr ha).trans hpa
    have hprod : 1 < a*p := by
      have hh := (div_lt_iff₀ ha).mp hpa
      nlinarith
    have hinv : 1/p < a := (div_lt_iff₀ hpp).mpr (by nlinarith)
    let c : ℝ := (a+1/p)/2
    have hc : 0 < c := by dsimp [c]; positivity
    have hca : c < a := by dsimp [c]; linarith
    have hh := (le_div_iff₀ hc).mp (hbound c hc hca)
    have hpc : 1 < p*c := by
      dsimp [c]
      have hpip : p*(1/p) = 1 := by field_simp
      nlinarith
    nlinarith
  change μ E ≤ ENNReal.ofReal (1/a)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ E)]
  exact ENNReal.ofReal_le_ofReal hp

theorem dominated_bounded_stopping {M R : ℕ → Ω → ℝ}
    (hM : Supermartingale M ℱ μ) (hzero : M 0 = 1)
    (hRm : ∀ n, AEStronglyMeasurable (R n) μ)
    (hRn : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ R n ω)
    (hdom : ∀ n, R n ≤ᵐ[μ] M n)
    (τ : Ω → ℕ) (hτ : IsStoppingTime ℱ τ) (N : ℕ) (hN : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue R τ) μ ∧ (∫ ω, stoppedValue R τ ω ∂μ) ≤ 1 := by
  have hRi (n : ℕ) : Integrable (R n) μ := by
    apply (hM.integrable n).mono' (hRm n)
    filter_upwards [hRn n,hdom n] with ω hn hd
    simpa [Real.norm_eq_abs,abs_of_nonneg hn] using hd
  have hRiτ := integrable_stoppedValue ℕ hτ hRi hN
  obtain ⟨hMiτ,hMeτ⟩ := supermartingale_bounded_stopping hM hzero τ hτ N hN
  refine ⟨hRiτ, (integral_mono_ae hRiτ hMiτ ?_).trans hMeτ⟩
  have hall : ∀ᵐ ω ∂μ, ∀ n, R n ω ≤ M n ω := (ae_all_iff).mpr hdom
  filter_upwards [hall] with ω hω
  exact hω (τ ω)

end
end EvidenceFusion
