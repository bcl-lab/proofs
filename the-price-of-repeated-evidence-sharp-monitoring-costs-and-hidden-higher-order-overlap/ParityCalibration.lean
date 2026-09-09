import ParitySources

open OverlapReconstruction ParityIncidence MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

theorem paritySourceB_active_count (m : ℕ) (i : Fin m) :
    (∑ v : ParitySource m (!(fullParity m)),
      if parityUses m (!(fullParity m)) v i ∧ oneMissing m v.1 = 1 then (1:ℤ) else 0) =
      (m-1:ℕ)*(m-1:ℕ) := by
  let b := !(fullParity m)
  have he (v : ParitySource m b) :
      (if parityUses m b v i ∧ oneMissing m v.1 = 1 then (1:ℤ) else 0) =
      if cubeExtends m (singletonCube m i) v.1 then oneMissing m v.1 else 0 := by
    rcases oneMissing_binary m v.1 with h | h <;>
      simp [h,cubeExtends_singleton,parityUses]
  calc
    _ = ∑ v : ParitySource m b,
        if cubeExtends m (singletonCube m i) v.1 then oneMissing m v.1 else 0 :=
      Finset.sum_congr rfl (fun v _ => he v)
    _ = _ := ?_
  have hs := paritySource_weight_sum m b
    (fun x => if cubeExtends m (singletonCube m i) x then oneMissing m x else 0)
  rw [hs]
  have hz := singleton_balancing_count m (singletonCube m i) (singletonCube_degree m i)
  rw [zeta_eq_pattern_sum] at hz
  simpa only [mul_ite,mul_zero] using hz

noncomputable def parityCertificate (m : ℕ) (v : ParitySource m (!(fullParity m))) : ℝ :=
  if oneMissing m v.1 = 1 then 1/((m-1:ℕ):ℝ)^2 else 0

theorem parityCertificate_nonnegative (m : ℕ) (v : ParitySource m (!(fullParity m))) :
    0 ≤ parityCertificate m v := by unfold parityCertificate; split_ifs <;> positivity

theorem parityCertificate_balance (m : ℕ) (hm : 2 ≤ m) (i : Fin m) :
    (∑ v : ParitySource m (!(fullParity m)),
      if parityUses m (!(fullParity m)) v i then parityCertificate m v else 0) = 1 := by
  have hd : (0:ℝ) < (m-1:ℕ) := by exact_mod_cast (show 0 < m-1 by omega)
  have hcount : (∑ v : ParitySource m (!(fullParity m)),
      if parityUses m (!(fullParity m)) v i ∧ oneMissing m v.1 = 1 then (1:ℝ) else 0) =
      ((m-1:ℕ):ℝ)^2 := by
    have h := congrArg (fun z : ℤ => (z:ℝ)) (paritySourceB_active_count m i)
    push_cast at h
    simpa only [pow_two] using h
  have he (v : ParitySource m (!(fullParity m))) :
      (if parityUses m (!(fullParity m)) v i then parityCertificate m v else 0) =
      (if parityUses m (!(fullParity m)) v i ∧ oneMissing m v.1 = 1 then (1:ℝ) else 0) /
        ((m-1:ℕ):ℝ)^2 := by
    unfold parityCertificate
    split_ifs <;> simp_all
  simp_rw [he]
  rw [← Finset.sum_div,hcount,div_self (pow_ne_zero 2 hd.ne')]

theorem paritySource_load (m : ℕ) (b : Bool) (a : ℝ) (v : ParitySource m b) :
    sourceLoad (parityUses m b) (fun _ => a) v = (degree m v.1:ℝ)*a := by
  have he : sourceLoad (parityUses m b) (fun _ => a) v =
      (∑ i : Fin m, if parityUses m b v i then (1:ℝ) else 0)*a := by
    rw [Finset.sum_mul]
    unfold sourceLoad
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [he,paritySource_read_sum]

/-- Exact finite cost of every opposite-parity system. -/
theorem paritySourceB_exact_cost (m : ℕ) (hm : 2 ≤ m) (a : ℝ) (ha : 0 < a)
    (ha1 : a < 1/((m-1:ℕ):ℝ)) :
    universalCost (parityUses m (!(fullParity m))) (fun _ => a) =
      ENNReal.ofReal ((1-((m-1:ℕ):ℝ)*a)^(-((m:ℝ)/((m-1:ℕ):ℝ)))) := by
  have hd : (0:ℝ) < (m-1:ℕ) := by exact_mod_cast (show 0 < m-1 by omega)
  have hL : ((m-1:ℕ):ℝ)*a < 1 := by
    have h := (lt_div_iff₀ hd).1 ha1
    nlinarith
  have hl : ∀ v, sourceLoad (parityUses m (!(fullParity m))) (fun _ => a) v ≤
      ((m-1:ℕ):ℝ)*a := by
    intro v
    rw [paritySource_load]
    apply mul_le_mul_of_nonneg_right _ ha.le
    exact_mod_cast (show degree m v.1 ≤ m-1 by have := paritySource_B_read_lt m v; omega)
  have hs : ∀ v, 0 < parityCertificate m v →
      sourceLoad (parityUses m (!(fullParity m))) (fun _ => a) v = ((m-1:ℕ):ℝ)*a := by
    intro v hv
    have hx : oneMissing m v.1 = 1 := by
      by_contra h
      simp [parityCertificate,h] at hv
    have hdg : degree m v.1 = m-1 := by have := oneMissing_degree m v.1 hx; omega
    rw [paritySource_load,hdg]
  have h := universalCost_weighted_gamma (parityUses m (!(fullParity m))) (fun _ => a)
    (parityCertificate m) (((m-1:ℕ):ℝ)*a) (fun _ => ha) (parityCertificate_nonnegative m)
    (mul_pos hd ha) hL hl (parityCertificate_balance m hm) hs
  have he : (∑ _ : Fin m, a)/(((m-1:ℕ):ℝ)*a) = (m:ℝ)/((m-1:ℕ):ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    exact mul_div_mul_right _ _ ha.ne'
  simpa only [he] using h

theorem paritySourceA_infinite (m : ℕ) (hm : 0 < m) (a : ℝ)
    (ha : 1/(m:ℝ) ≤ a) :
    universalCost (parityUses m (fullParity m)) (fun _ => a) = ∞ := by
  classical
  apply universalCost_infinite_of_source_load _ _ (paritySourceA_full m hm)
  rw [paritySource_load]
  change 1 ≤ (degree m (full m):ℝ)*a
  rw [degree_full]
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have h := (div_le_iff₀ hm').1 ha
  nlinarith

end RepeatedEvidenceProbability
