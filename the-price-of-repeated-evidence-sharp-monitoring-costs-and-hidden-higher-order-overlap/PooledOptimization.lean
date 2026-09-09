import PooledStructure

set_option maxHeartbeats 1500000

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem finnerFirst_negative (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    RepeatedEvidence.finnerFirst a b < 0 := by
  have hb := ha.trans hab
  have hba := sub_pos.mpr hab
  have hy : 0 < b/(b-a) := div_pos hb hba
  have hy1 : b/(b-a) ≠ 1 := by
    intro h
    have := (div_eq_one_iff_eq hba.ne').mp h
    linarith
  have hl := Real.log_lt_sub_one_of_pos hy hy1
  have hinv : (1-a/b)⁻¹ = b/(b-a) := by field_simp <;> ring
  have hid : b/(b-a)-1 = a/(b-a) := by field_simp <;> ring
  rw [hid] at hl
  have hlog : -Real.log (1-a/b) = Real.log (b/(b-a)) := by
    rw [← hinv,Real.log_inv]
  unfold RepeatedEvidence.finnerFirst
  rw [hlog]
  exact sub_neg.mpr hl

theorem finnerTerm_strictAnti (a : ℝ) (ha : 0 < a) :
    StrictAntiOn (RepeatedEvidence.finnerTerm a) (Ioi a) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi a)
  · intro b hb
    exact (RepeatedEvidence.finner_first_derivative a b ha hb).continuousAt.continuousWithinAt
  · intro b hb
    have hab : a < b := by simpa using hb
    rw [(RepeatedEvidence.finner_first_derivative a b ha hab).deriv]
    exact finnerFirst_negative a b ha hab

def pooledWeights {J : Type} (b : ℝ) : Option J → ℝ
  | none => b
  | some _ => 1-b

theorem pooledWeights_feasible {J : Type} [Fintype J] [DecidableEq J]
    (a₀ c b : ℝ) (hb : b ∈ Ioo a₀ (1-c)) :
    pooledWeights b ∈ RepeatedEvidence.finnerDomain (@pooledUses J)
      (pooledPowers a₀ (fun _ => c)) := by
  constructor
  · intro i
    cases i with
    | none => exact hb.1
    | some j => dsimp [pooledPowers,pooledWeights]; linarith [hb.2]
  · intro v
    simp [Fintype.sum_option,pooledUses,pooledWeights]

theorem pooled_saturation_le {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ c : ℝ) (ha₀ : 0 < a₀) (hc : 0 < c) (β : Option J → ℝ)
    (hβ : β ∈ RepeatedEvidence.finnerDomain pooledUses (pooledPowers a₀ (fun _ => c))) :
    β none ∈ Ioo a₀ (1-c) ∧
    RepeatedEvidence.finnerObjective (pooledPowers a₀ (fun _ : J => c))
      (pooledWeights (β none)) ≤
      RepeatedEvidence.finnerObjective (pooledPowers a₀ (fun _ : J => c)) β := by
  have hle : ∀ j, β (some j) ≤ 1-β none := by
    intro j
    have h := hβ.2 j
    simp [Fintype.sum_option,pooledUses] at h
    linarith
  have hlt : c < 1-β none := (hβ.1 (some (Classical.arbitrary J))).trans_le (hle _)
  refine ⟨⟨hβ.1 none,by linarith⟩,?_⟩
  apply Finset.sum_le_sum
  intro i _
  cases i with
  | none => exact le_rfl
  | some j =>
    exact (finnerTerm_strictAnti c hc).antitoneOn (hβ.1 (some j)) hlt (hle j)

noncomputable def pooledFinnerValue (k : ℕ) (a₀ c b : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (1/(1-a₀/b)))^b *
    (ENNReal.ofReal (1/(1-c/(1-b))))^((k:ℝ)*(1-b))

theorem pooledFinnerValue_eq {J : Type} [Fintype J] (a₀ c b : ℝ) :
    finnerBoundValue (pooledPowers a₀ (fun _ : J => c)) (pooledWeights b) =
      pooledFinnerValue (Fintype.card J) a₀ c b := by
  simp only [finnerBoundValue,Fintype.prod_option,pooledPowers,pooledWeights,
    Finset.prod_const,Finset.card_univ,pooledFinnerValue]
  rw [mul_comm (Fintype.card J : ℝ) (1-b),ENNReal.rpow_mul_natCast]

/-- The scalar infimum displayed in Corollary 5 is attained at an interior
point and equals the actual optimized Finner functional. -/
theorem pooledFinner_scalar_minimum {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (a₀ c : ℝ) (ha₀ : 0 < a₀) (hc : 0 < c) (hsub : a₀+c < 1) :
    ∃ b ∈ Ioo a₀ (1-c),
      pooledFinnerValue (Fintype.card J) a₀ c b =
        optimizedFinnerCost pooledUses (pooledPowers a₀ (fun _ : J => c)) ∧
      ∀ t ∈ Ioo a₀ (1-c), pooledFinnerValue (Fintype.card J) a₀ c b ≤
        pooledFinnerValue (Fintype.card J) a₀ c t := by
  have ha : ∀ i : Option J, 0 < pooledPowers a₀ (fun _ => c) i := by
    intro i; cases i <;> assumption
  have hstudy : ∀ i : Option J, ∃ v, pooledUses v i := by
    intro i
    cases i with
    | none => exact ⟨Classical.arbitrary J,True.intro⟩
    | some j => exact ⟨j,rfl⟩
  have hload : ∀ v : J, sourceLoad pooledUses (pooledPowers a₀ (fun _ => c)) v < 1 := by
    intro v; simpa only [pooled_source_load] using hsub
  obtain ⟨β,⟨hβ,heq⟩,_⟩ := optimizedFinnerCost_unique_attainment pooledUses
    (pooledPowers a₀ (fun _ : J => c)) ha hstudy hload
  obtain ⟨hb,hobj⟩ := pooled_saturation_le a₀ c ha₀ hc β hβ
  have hs := pooledWeights_feasible (J:=J) a₀ c (β none) hb
  have hval : finnerBoundValue (pooledPowers a₀ (fun _ : J => c)) (pooledWeights (β none)) ≤
      finnerBoundValue (pooledPowers a₀ (fun _ : J => c)) β := by
    rw [finnerBoundValue_eq_exp_objective pooledUses _ _ ha hs,
      finnerBoundValue_eq_exp_objective pooledUses _ _ ha hβ]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hobj)
  have hlo : ∀ t ∈ Ioo a₀ (1-c),
      optimizedFinnerCost pooledUses (pooledPowers a₀ (fun _ : J => c)) ≤
        pooledFinnerValue (Fintype.card J) a₀ c t := by
    intro t ht
    rw [← pooledFinnerValue_eq (J:=J)]
    exact iInf_le (fun β : {β // β ∈ RepeatedEvidence.finnerDomain
      (@pooledUses J) (pooledPowers a₀ (fun _ : J => c))} =>
        finnerBoundValue (pooledPowers a₀ (fun _ : J => c)) β.val)
      ⟨pooledWeights t,pooledWeights_feasible (J:=J) a₀ c t ht⟩
  rw [pooledFinnerValue_eq,heq] at hval
  have he : pooledFinnerValue (Fintype.card J) a₀ c (β none) =
      optimizedFinnerCost pooledUses (pooledPowers a₀ (fun _ : J => c)) :=
    le_antisymm hval (hlo _ hb)
  exact ⟨β none,hb,he,fun t ht => he.le.trans (hlo t ht)⟩

end RepeatedEvidenceProbability
