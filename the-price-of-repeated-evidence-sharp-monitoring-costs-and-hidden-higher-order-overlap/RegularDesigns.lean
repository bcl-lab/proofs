import WeightedGammaAttainment

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

/-- The manuscript's regular-design corollary, with its uniform source
certificate explicitly instantiated. Both exact costs are obtained. -/
theorem regular_design_exact_cost {V I : Type} [Fintype V] [Fintype I]
    (A : V → I → Prop) [DecidableRel A] (k d : ℕ) (hk : 0 < k) (hd : 0 < d)
    (hstudy : ∀ i, (∑ v, if A v i then (1:ℝ) else 0) = k)
    (hsource : ∀ v, (∑ i, if A v i then (1:ℝ) else 0) = d)
    (a : ℝ) (ha : 0 < a) (had : a < 1/(d:ℝ)) :
    universalCost A (fun _ => a) = ENNReal.ofReal ((1-(d:ℝ)*a)^(-(Fintype.card I:ℝ)/(d:ℝ))) ∧
      optimizedFinnerCost A (fun _ => a) =
        ENNReal.ofReal ((1-(d:ℝ)*a)^(-(Fintype.card I:ℝ)/(d:ℝ))) := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hload : ∀ v, sourceLoad A (fun _ => a) v = (d:ℝ)*a := by
    intro v
    unfold sourceLoad
    calc
      _ = (∑ i, if A v i then (1:ℝ) else 0)*a := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp
      _ = _ := by rw [hsource]
  have hbal : ∀ i, (∑ v, if A v i then 1/(k:ℝ) else 0) = 1 := by
    intro i
    calc
      _ = (∑ v, if A v i then (1:ℝ) else 0)/(k:ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro v _
        split_ifs <;> simp
      _ = 1 := by rw [hstudy]; exact div_self hk0.ne'
  have hL : (d:ℝ)*a < 1 := by
    have := (lt_div_iff₀ hd0).mp had
    nlinarith
  have h := weighted_gamma_attainment A (fun _ => a) (fun _ => 1/(k:ℝ)) ((d:ℝ)*a)
    (fun _ => ha) (fun _ => (one_div_pos.mpr hk0).le) (mul_pos hd0 ha) hL
    (fun v => (hload v).le) hbal (fun v _ => hload v)
  have he : -((∑ _ : I, a)/((d:ℝ)*a)) = -(Fintype.card I:ℝ)/(d:ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp
    ring
  simpa only [he] using h

end RepeatedEvidenceProbability
