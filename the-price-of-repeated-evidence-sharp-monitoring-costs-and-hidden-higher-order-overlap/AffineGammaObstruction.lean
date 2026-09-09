import GammaSums

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

namespace RepeatedEvidenceProbability

/-- The logarithms of an exponential and a shifted, scaled gamma moment
function cannot agree near zero for shape greater than one. -/
theorem gamma_log_mgf_not_affine_exponential (k ℓ d : ℝ) (hk : 1 < k) (hℓ : 0 < ℓ) :
    ¬ (fun p : ℝ => -Real.log (1-p)) =ᶠ[𝓝 0]
      (fun p => d*p-k*Real.log (1-ℓ*p)) := by
  intro he
  have hder₁ (p : ℝ) (hp : 1-p ≠ 0) :
      HasDerivAt (fun p : ℝ => -Real.log (1-p)) (1/(1-p)) p := by
    convert (((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)).log hp).neg using 1 <;> simp [one_div] <;> ring
  have hder₂ (p : ℝ) (hp : 1-ℓ*p ≠ 0) :
      HasDerivAt (fun p : ℝ => d*p-k*Real.log (1-ℓ*p)) (d+k*ℓ/(1-ℓ*p)) p := by
    convert ((hasDerivAt_id p).const_mul d).sub
      ((((hasDerivAt_const p (1:ℝ)).sub ((hasDerivAt_id p).const_mul ℓ)).log hp).const_mul k) using 1
    simp only [id_eq]
    field_simp <;> ring
  have hn₁ : ∀ᶠ p : ℝ in 𝓝 0, 1-p ≠ 0 := by
    exact ((continuous_const.sub continuous_id).continuousAt.eventually_ne (by norm_num))
  have hn₂ : ∀ᶠ p : ℝ in 𝓝 0, 1-ℓ*p ≠ 0 := by
    exact ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne (by simp))
  have he₁ : (fun p : ℝ => 1/(1-p)) =ᶠ[𝓝 0]
      (fun p => d+k*ℓ/(1-ℓ*p)) := by
    have hd := he.deriv
    filter_upwards [hd,hn₁,hn₂] with p hp hp₁ hp₂
    simpa only [(hder₁ p hp₁).deriv,(hder₂ p hp₂).deriv] using hp
  have hd₁ (p : ℝ) (hp : 1-p ≠ 0) :
      HasDerivAt (fun p : ℝ => 1/(1-p)) (1/(1-p)^2) p := by
    convert (hasDerivAt_const p (1:ℝ)).div
      ((hasDerivAt_const p (1:ℝ)).sub (hasDerivAt_id p)) hp using 1 <;> simp
  have hd₂ (p : ℝ) (hp : 1-ℓ*p ≠ 0) :
      HasDerivAt (fun p : ℝ => d+k*ℓ/(1-ℓ*p)) (k*ℓ^2/(1-ℓ*p)^2) p := by
    convert ((hasDerivAt_const p (k*ℓ)).div
      ((hasDerivAt_const p (1:ℝ)).sub ((hasDerivAt_id p).const_mul ℓ)) hp).const_add d using 1
    simp only [id_eq]
    ring
  have he₂ : (fun p : ℝ => 1/(1-p)^2) =ᶠ[𝓝 0]
      (fun p => k*ℓ^2/(1-ℓ*p)^2) := by
    have hd := he₁.deriv
    filter_upwards [hd,hn₁,hn₂] with p hp hp₁ hp₂
    simpa only [(hd₁ p hp₁).deriv,(hd₂ p hp₂).deriv] using hp
  have hval := he₂.eq_of_nhds
  simp only [mul_zero,sub_zero,one_pow,div_one] at hval
  have he₃ := he₂.deriv.eq_of_nhds
  have hdd₁ : HasDerivAt (fun p : ℝ => 1/(1-p)^2) 2 0 := by
    convert (hasDerivAt_const (0:ℝ) (1:ℝ)).div
      (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ))).pow 2) (by norm_num) using 1 <;> norm_num
  have hdd₂ : HasDerivAt (fun p : ℝ => k*ℓ^2/(1-ℓ*p)^2) (2*k*ℓ^3) 0 := by
    convert (hasDerivAt_const (0:ℝ) (k*ℓ^2)).div
      (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub ((hasDerivAt_id (0:ℝ)).const_mul ℓ)).pow 2) (by simp) using 1
    simp only [id_eq]
    ring
  rw [hdd₁.deriv,hdd₂.deriv] at he₃
  have hℓ1 : ℓ = 1 := by nlinarith [sq_nonneg ℓ]
  rw [hℓ1] at hval
  norm_num at hval
  linarith


/-- An exponential variable cannot be an affine function of a gamma variable
of shape greater than one. This avoids any equality-case premise. -/
theorem exponential_not_affine_gamma {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E G : Ω → ℝ)
    (hE : Measurable E) (hG : Measurable G) (k : ℝ) (hk : 1 < k)
    (hlawE : μ.map E = expMeasure 1) (hlawG : μ.map G = gammaShapeMeasure k)
    (ℓ d : ℝ) (hℓ : 0 < ℓ) : ¬ E =ᵐ[μ] (fun ω => ℓ*G ω+d) := by
  intro he
  have hm (p : ℝ) (hp : p < 1) (hpl : ℓ*p < 1) :
      (1-p)^(-(1:ℝ)) = (1-ℓ*p)^(-k)*Real.exp (p*d) := by
    have hExp : mgf E μ p = (1-p)^(-(1:ℝ)) := by
      rw [← mgf_id_map hE.aemeasurable,hlawE]
      have h := gammaShape_mgf 1 p (by norm_num) hp
      simpa [gammaShapeMeasure,expMeasure] using h
    have hGamma : mgf G μ (ℓ*p) = (1-ℓ*p)^(-k) := by
      rw [← mgf_id_map hG.aemeasurable,hlawG]
      exact gammaShape_mgf k _ (by linarith) hpl
    calc
      _ = mgf E μ p := hExp.symm
      _ = mgf (fun ω => ℓ*G ω+d) μ p := mgf_congr he
      _ = mgf (ℓ • G) μ p * Real.exp (p*d) := mgf_add_const d
      _ = _ := by rw [mgf_smul_left,hGamma]
  apply gamma_log_mgf_not_affine_exponential k ℓ d hk hℓ
  have hn₁ : ∀ᶠ p : ℝ in 𝓝 0, 0 < 1-p :=
    (continuous_const.sub continuous_id).continuousAt.eventually (Ioi_mem_nhds (by norm_num))
  have hn₂ : ∀ᶠ p : ℝ in 𝓝 0, 0 < 1-ℓ*p :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
      (Ioi_mem_nhds (by simp))
  filter_upwards [hn₁,hn₂] with p hp hpℓ
  have h := congrArg Real.log (hm p (by linarith) (by linarith))
  rw [Real.log_mul (Real.rpow_pos_of_pos hpℓ _).ne' (Real.exp_pos _).ne',
    Real.log_rpow hp,Real.log_rpow hpℓ,Real.log_exp] at h
  nlinarith

end RepeatedEvidenceProbability

