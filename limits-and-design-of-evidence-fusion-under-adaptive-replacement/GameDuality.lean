import CompleteClass
import Mathlib.Analysis.Convex.Topology

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Nonempty ι] [Nonempty κ]

def gameUpper (B : κ → ι → ℝ) (w : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => ∑ i, w i*B j i)

/-- Strong finite game duality, with attained normalized primal and dual
strategies. No linear-programming duality statement is a premise. -/
theorem finite_game_duality (B : κ → ι → ℝ) :
    ∃ (r : ℝ) (w : ι → ℝ) (q : κ → ℝ),
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j = 1) ∧
      (∀ j, ∑ i, w i*B j i ≤ r) ∧ (∀ i, r ≤ ∑ j, q j*B j i) := by
  have hcont : Continuous (gameUpper B) := by
    apply Continuous.finset_sup'_apply Finset.univ_nonempty
    intro j _
    exact continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  have hne : (stdSimplex ℝ ι).Nonempty := ⟨Pi.single i0 1,single_mem_stdSimplex ℝ i0⟩
  obtain ⟨w,hw,hmin⟩ := (isCompact_stdSimplex ι).exists_isMinOn hne hcont.continuousOn
  let r := gameUpper B w
  let S : Set (κ → ℝ) := {z | ∀ j, z j < r}
  let T : Set (κ → ℝ) := {z | ∃ v ∈ stdSimplex ℝ ι, z = fun j => ∑ i, v i*B j i}
  have hSc : Convex ℝ S := by
    intro x hx y hy a b ha hb hab j
    change a*x j+b*y j < r
    have h1 := mul_nonneg ha (sub_pos.mpr (hx j)).le
    have h2 := mul_nonneg hb (sub_pos.mpr (hy j)).le
    have habr : (a+b)*r = r := by rw [hab,one_mul]
    rcases lt_or_eq_of_le ha with hap | rfl
    · have := mul_pos hap (sub_pos.mpr (hx j)); nlinarith
    · have : b = 1 := by linarith
      simpa [this] using hy j
  have hSo : IsOpen S := by
    have he : S = ⋂ j, {z : κ → ℝ | z j < r} := by ext z; simp [S]
    rw [he]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (continuous_apply j) continuous_const)
  have hTc : Convex ℝ T := by
    rintro x ⟨v,hv,rfl⟩ y ⟨z,hz,rfl⟩ a b ha hb hab
    refine ⟨a • v+b • z,(convex_stdSimplex ℝ ι) hv hz ha hb hab,?_⟩
    funext j
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib]
    simp_rw [mul_assoc,← Finset.mul_sum]
  have hdis : Disjoint S T := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨v,hv,rfl⟩
    have hr := hmin hv
    have ht : gameUpper B v < r := by
      obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset κ))
        Finset.univ_nonempty (fun j => ∑ i, v i*B j i)
      change (Finset.univ.sup' Finset.univ_nonempty (fun j => ∑ i, v i*B j i)) < r
      rw [he]
      exact hz j
    exact (not_lt_of_ge hr) ht
  obtain ⟨L,u,hS,hT⟩ := geometric_hahn_banach_open hSc hSo hTc hdis
  let v : κ → ℝ := fun j => L (Pi.single j 1)
  have hexp (z : κ → ℝ) : L z = ∑ j, v j*z j := by
    have he : z = ∑ j, z j • (Pi.single j (1 : ℝ) : κ → ℝ) := by
      funext j; simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]
    conv_lhs => rw [he]
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hv (j : κ) : 0 ≤ v j := by
    have hh : -v j ≤ 0 := slope_comparison (a := (r-1)*∑ i, v i) (b := u)
      (w := -v j) (v := 0) (by
        intro t ht
        have hz := hS (fun i => (r-1) - if i=j then t else 0) (by
          intro i
          change (r-1)-(if i=j then t else 0) < r
          split_ifs <;> linarith)
        rw [hexp] at hz
        simp_rw [mul_sub,Finset.sum_sub_distrib] at hz
        simp only [← Finset.sum_mul] at hz
        simp [mul_ite] at hz
        nlinarith)
    linarith
  let V := ∑ j, v j
  have hVn : 0 ≤ V := Finset.sum_nonneg (fun j _ => hv j)
  have hV : 0 < V := by
    by_contra hnot
    have hz : V = 0 := le_antisymm (le_of_not_gt hnot) hVn
    have hvz (j : κ) : v j = 0 := by
      have hh := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hv i) (Finset.mem_univ j)
      change v j ≤ V at hh
      rw [hz] at hh
      exact le_antisymm hh (hv j)
    have hs := hS (fun _ => r-1) (fun _ => by change r-1 < r; linarith)
    have ht := hT (fun j => ∑ i, w i*B j i) ⟨w,hw,rfl⟩
    simp [hexp,hvz] at hs ht
    linarith
  have hboundary : r*V ≤ u := by
    by_contra hnot
    let e := (r*V-u)/(2*V)
    have he : 0 < e := div_pos (sub_pos.mpr (lt_of_not_ge hnot)) (by positivity)
    have hh := hS (fun _ => r-e) (fun _ => by change r-e < r; linarith)
    rw [hexp,← Finset.sum_mul] at hh
    have heq : e*(2*V) = r*V-u := by dsimp [e]; field_simp
    change V*(r-e) < u at hh
    nlinarith
  let q := fun j => v j/V
  refine ⟨r,w,q,hw.1,hw.2,fun j => div_nonneg (hv j) hV.le,?_,?_,?_⟩
  · dsimp [q]; rw [← Finset.sum_div]; exact div_self hV.ne'
  · intro j
    exact Finset.le_sup' (fun j => ∑ i, w i*B j i) (Finset.mem_univ j)
  · intro i
    have ht := hT (fun j => B j i) ⟨Pi.single i 1,single_mem_stdSimplex ℝ i,by
      funext j; simp [Pi.single_apply]⟩
    rw [hexp] at ht
    have heq : (∑ j, q j*B j i) = (∑ j, v j*B j i)/V := by
      dsimp [q]; simp_rw [div_mul_eq_mul_div]; rw [Finset.sum_div]
    rw [heq]
    exact (le_div_iff₀ hV).mpr (hboundary.trans ht)

end
end EvidenceFusion
