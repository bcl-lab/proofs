import GameDuality
import Cardinality

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Nonempty ι] [Nonempty κ]

def fractionalCoverValues (B : κ → ι → ℝ) : Set ℝ :=
  {v | ∃ z : κ → ℝ, (∀ j, 0 ≤ z j) ∧ (∀ i, 1 ≤ ∑ j, z j*B j i) ∧ v=∑ j, z j}

/-- Strong game duality plus the exact fractional-cover scaling. In the
independent-set incidence matrix this is the fractional chromatic identity. -/
theorem fractional_cover_duality (B : κ → ι → ℝ) (hB : ∀ j i, 0 ≤ B j i)
    (hcover : ∀ i, ∃ j, 0 < B j i) :
    ∃ (r : ℝ) (w : ι → ℝ), 0 < r ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
      gameUpper B w=r ∧ (∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → (∑ i, v i=1) → r ≤ gameUpper B v) ∧
      IsLeast (fractionalCoverValues B) (1/r) := by
  obtain ⟨r,w,q,hw,hws,hq,hqs,hupper,hlower⟩ := finite_game_duality B
  have hr : 0 < r := by
    have hwpos : ∃ i, 0 < w i := by
      by_contra hn
      push_neg at hn
      have he : ∑ i, w i=0 := Finset.sum_eq_zero (fun i _ => le_antisymm (hn i) (hw i))
      linarith
    obtain ⟨i,hi⟩ := hwpos
    obtain ⟨j,hj⟩ := hcover i
    have hh := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => mul_nonneg (hw l) (hB j l))
      (Finset.mem_univ i)
    exact (mul_pos hi hj).trans_le (hh.trans (hupper j))
  have hmin (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i, v i=1) : r ≤ gameUpper B v :=
    game_weak_duality v q B r (gameUpper B v) hv hq hvs hqs hlower
      (fun j => Finset.le_sup' (fun j => ∑ i, v i*B j i) (Finset.mem_univ j))
  have he : gameUpper B w=r := le_antisymm
    (Finset.sup'_le Finset.univ_nonempty _ (fun j _ => hupper j)) (hmin w hw hws)
  refine ⟨r,w,hr,hw,hws,he,hmin,?_,?_⟩
  · refine ⟨fun j => q j/r,fun j => div_nonneg (hq j) hr.le,?_,?_⟩
    · intro i
      simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
      exact (le_div_iff₀ hr).mpr (by simpa using hlower i)
    · rw [← Finset.sum_div,hqs]
  · rintro v ⟨z,hz,hzc,rfl⟩
    have hh := game_weak_duality w (fun j => z j/(∑ l, z l)) B
      (1/(∑ l, z l)) r hw
    have hmass : 0 < ∑ j, z j := by
      obtain ⟨i⟩ := (inferInstance : Nonempty ι)
      have hi := hzc i
      have hn : 0 ≤ ∑ j, z j := Finset.sum_nonneg (fun j _ => hz j)
      by_contra hp
      have hez : ∀ j, z j=0 := by
        intro j
        have hb := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hz l) (Finset.mem_univ j)
        exact le_antisymm (hb.trans (le_of_not_gt hp)) (hz j)
      simp [hez] at hi
      linarith
    have hineq := hh (fun j => div_nonneg (hz j) hmass.le) hws
      (by rw [← Finset.sum_div]; exact div_self hmass.ne')
      (fun i => by
        simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
        exact div_le_div_of_nonneg_right (hzc i) hmass.le) hupper
    have hm := (div_le_iff₀ hmass).mp hineq
    exact (div_le_iff₀ hr).mpr (by nlinarith)

def domainMass (g : ι → κ) (w : ι → ℝ) (j : κ) : ℝ :=
  ∑ i, if g i=j then w i else 0

theorem domainMass_total (g : ι → κ) (w : ι → ℝ) :
    (∑ j, domainMass g w j)=∑ i, w i := by
  unfold domainMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem equal_domain_allocation (g : ι → κ) (hg : Function.Surjective g) :
    ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ (∑ i, w i=1) ∧
      ∀ j, domainMass g w j=1/(Fintype.card κ : ℝ) := by
  let N := fun j => (Finset.univ.filter (fun i => g i=j)).card
  have hN (j : κ) : 0 < N j := by
    apply Finset.card_pos.mpr
    obtain ⟨i,hi⟩ := hg j
    exact ⟨i,by simp [hi]⟩
  have hG : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  let w := fun i => (1/(Fintype.card κ : ℝ))/(N (g i) : ℝ)
  have hw (i : ι) : 0 < w i := div_pos (one_div_pos.mpr hG) (by exact_mod_cast hN (g i))
  have hm (j : κ) : domainMass g w j=1/(Fintype.card κ : ℝ) := by
    have he : domainMass g w j=∑ i ∈ Finset.univ.filter (fun i => g i=j),
        (1/(Fintype.card κ : ℝ))/(N j : ℝ) := by
      unfold domainMass
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : g i=j <;> simp [hi,w]
    rw [he]
    simp only [Finset.sum_const,nsmul_eq_mul]
    change (N j : ℝ)*((1/(Fintype.card κ : ℝ))/(N j : ℝ))=1/(Fintype.card κ : ℝ)
    have hNr : (N j : ℝ) ≠ 0 := by exact_mod_cast (hN j).ne'
    field_simp [hNr,hG.ne']
    ring
  refine ⟨w,hw,?_,hm⟩
  rw [← domainMass_total g w]
  simp only [hm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp

theorem failure_domain_game (g : ι → κ) (hg : Function.Surjective g) :
    IsLeast {v | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
      v=gameUpper (fun j i => if g i=j then 1 else 0) w} (1/(Fintype.card κ : ℝ)) := by
  have he (w : ι → ℝ) (j : κ) : (∑ i, w i*(if g i=j then (1 : ℝ) else 0))=domainMass g w j := by
    simp [domainMass,mul_ite]
  constructor
  · obtain ⟨w,hw,hs,hm⟩ := equal_domain_allocation g hg
    refine ⟨w,fun i => (hw i).le,hs,?_⟩
    unfold gameUpper
    simp only [he,hm]
    simp
  · rintro v ⟨w,hw,hs,rfl⟩
    have hb : (1 : ℝ) ≤ ∑ _j : κ, gameUpper (fun j i => if g i=j then 1 else 0) w := by
      calc
        1 = ∑ j, domainMass g w j := by rw [domainMass_total,hs]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j _
          rw [← he]
          exact Finset.le_sup' (fun j => ∑ i, w i*(if g i=j then (1 : ℝ) else 0)) (Finset.mem_univ j)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hb
    have hG : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
    exact (div_le_iff₀ hG).mpr (by nlinarith)

end
end EvidenceFusion
