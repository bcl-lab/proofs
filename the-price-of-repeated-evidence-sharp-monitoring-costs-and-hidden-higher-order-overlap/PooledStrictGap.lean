import EqualLeafGamma
import StrictHolder
import ExponentNonproportionality
import PooledOptimization

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

/-- Strict comparison at every interior fractional weight. The equality
case is excluded by the second and third derivatives of the log MGF. -/
theorem pooled_cost_strict_at_weight {J : Type} [Fintype J] [DecidableEq J]
    (hJ : 2 ≤ Fintype.card J) (a₀ c b : ℝ) (ha₀ : 0 < a₀) (hc : 0 < c)
    (hb : b ∈ Ioo a₀ (1-c)) :
    universalCost pooledUses (pooledPowers a₀ (fun _ : J => c)) <
      pooledFinnerValue (Fintype.card J) a₀ c b := by
  haveI : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  have hb0 : 0 < b := ha₀.trans hb.1
  have hb1 : b < 1 := by linarith [hb.2]
  have hb' : 0 < 1-b := sub_pos.mpr hb1
  let α := a₀/b
  let β := c/(1-b)
  have hα : 0 < α := div_pos ha₀ hb0
  have hβ : 0 < β := div_pos hc hb'
  have hα1 : α < 1 := (div_lt_one hb0).mpr hb.1
  have hβ1 : β < 1 := (div_lt_one hb').mpr (by linarith [hb.2])
  let E := pooledSurvivalTime (fun _ : J => c)
  let G := leafSum J
  have hE : Measurable E := pooledTimes_measurable (fun _ : J => c) none
  have hG : Measurable G := leafSum_measurable J
  have hlawE : (exponentialProduct J).map E = expMeasure 1 :=
    pooledTimes_law (fun _ : J => c) (fun _ => hc.ne') none
  have hlawG : (exponentialProduct J).map G = gammaShapeMeasure (Fintype.card J) := leafSum_gamma_law J
  let A := 1/(1-α)
  let B := (1/(1-β))^(Fintype.card J : ℝ)
  have hA : 0 < A := one_div_pos.mpr (sub_pos.mpr hα1)
  have hBase : 0 < 1/(1-β) := one_div_pos.mpr (sub_pos.mpr hβ1)
  have hB : 0 < B := Real.rpow_pos_of_pos hBase _
  have hmA : (∫⁻ x, ENNReal.ofReal (Real.exp (α*E x)) ∂exponentialProduct J) = ENNReal.ofReal A :=
    exponential_law_moment _ E hE hlawE α hα1
  have hmB : (∫⁻ x, ENNReal.ofReal (Real.exp (β*G x)) ∂exponentialProduct J) = ENNReal.ofReal B :=
    leafSum_exponential_moment J β hβ1
  have hk : (1:ℝ) < Fintype.card J := by exact_mod_cast (show 1 < Fintype.card J by omega)
  have hne := exponential_gamma_nonproportional (exponentialProduct J) E G hE hG
    (Fintype.card J) hk hlawE hlawG α β A B hα hβ hA hB
  have hs := holder_strict (exponentialProduct J)
    (fun x => Real.exp (α*E x)) (fun x => Real.exp (β*G x))
    (measurable_const.mul hE).exp (measurable_const.mul hG).exp
    (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _)
    A B hA hB hmA hmB b hb0 hb1 hne
  have hcost : universalCost pooledUses (pooledPowers a₀ (fun _ : J => c)) =
      ∫⁻ x, ENNReal.ofReal ((Real.exp (α*E x))^b*(Real.exp (β*G x))^(1-b)) ∂exponentialProduct J := by
    rw [pooled_equal_leaf_cost_integral J a₀ c ha₀ hc]
    apply lintegral_congr
    intro x
    rw [← Real.exp_mul,← Real.exp_mul,← Real.exp_add]
    congr 2
    dsimp [α,β,E,G]
    field_simp
  have hbound : ENNReal.ofReal (A^b*B^(1-b)) = pooledFinnerValue (Fintype.card J) a₀ c b := by
    rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hA b).le]
    dsimp [B]
    rw [← Real.rpow_mul hBase.le]
    rw [← ENNReal.ofReal_rpow_of_pos hA,← ENNReal.ofReal_rpow_of_pos hBase]
    rfl
  exact hcost.le.trans_lt (hs.trans_eq hbound)

/-- Corollary 5, stated against the actual optimized Finner infimum. -/
theorem pooled_strict_optimized_gap {J : Type} [Fintype J] [DecidableEq J]
    (hJ : 2 ≤ Fintype.card J) (a₀ c : ℝ) (ha₀ : 0 < a₀) (hc : 0 < c)
    (hsub : a₀+c < 1) :
    universalCost pooledUses (pooledPowers a₀ (fun _ : J => c)) <
      optimizedFinnerCost pooledUses (pooledPowers a₀ (fun _ : J => c)) := by
  haveI : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b,hb,heq,_⟩ := pooledFinner_scalar_minimum (J:=J) a₀ c ha₀ hc hsub
  rw [← heq]
  exact pooled_cost_strict_at_weight hJ a₀ c b ha₀ hc hb

end RepeatedEvidenceProbability
