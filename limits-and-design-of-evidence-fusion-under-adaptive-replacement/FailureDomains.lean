import FamilyDesign

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Nonempty ι] [Nonempty κ]

def domainAttacks (g : ι → κ) : Finset (Finset ι) :=
  Finset.univ.filter (fun C => ∃ j, ∀ i ∈ C, g i=j)

theorem domainAttacks_nonempty (g : ι → κ) : (domainAttacks g).Nonempty := by
  obtain ⟨j⟩ := (inferInstance : Nonempty κ)
  exact ⟨∅,by simp [domainAttacks]⟩

theorem domainAttacks_downward (g : ι → κ) : DownwardClosed (domainAttacks g) := by
  intro C hC B hBC
  obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hC).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,fun i hi => hj i (hBC hi)⟩

theorem domain_removable_weight (g : ι → κ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (domainAttacks g).sup' (domainAttacks_nonempty g) (fun C => ∑ i ∈ C, w i) =
      gameUpper (fun j i => if g i=j then 1 else 0) w := by
  have he (j : κ) : (∑ i, w i*(if g i=j then (1 : ℝ) else 0))=domainMass g w j := by
    simp [domainMass,mul_ite]
  apply le_antisymm
  · apply Finset.sup'_le (domainAttacks_nonempty g)
    intro C hC
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hC).2
    have hs : C ⊆ Finset.univ.filter (fun i => g i=j) := by intro i hi; simp [hj i hi]
    have hh := Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => hw i)
    have he' : (∑ i ∈ Finset.univ.filter (fun i => g i=j), w i)=domainMass g w j := by
      simp [domainMass,Finset.sum_filter]
    rw [he',← he] at hh
    exact hh.trans (Finset.le_sup' (fun j => ∑ i, w i*(if g i=j then (1 : ℝ) else 0))
      (Finset.mem_univ j))
  · apply Finset.sup'_le Finset.univ_nonempty
    intro j _
    let C := Finset.univ.filter (fun i => g i=j)
    have hC : C ∈ domainAttacks g := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,j,fun i hi => (Finset.mem_filter.mp hi).2⟩
    have hh := Finset.le_sup' (fun C => ∑ i ∈ C, w i) hC
    rw [he]
    simpa [C,domainMass,Finset.sum_filter] using hh

theorem positive_domain_admissibility [Nontrivial κ] (g : ι → κ)
    (hg : Function.Surjective g) (a : ℝ) (w : ι → ℝ) (ha : 0 ≤ a)
    (hw : ∀ i, 0 < w i) (hn : a+∑ i, w i=1) :
    ProbabilityAdmissible (domainAttacks g)
      (fun y => robustAffine a w y (domainAttacks g) (domainAttacks_nonempty g)) := by
  apply (exact_probability_admissibility _ _ (domainAttacks_downward g) a w ha
    (fun i => (hw i).le) hn).mpr
  have hs : positiveSupport w=Finset.univ := by ext i; simp [positiveSupport,hw i]
  have hp : projectedAttacks (domainAttacks g) w=domainAttacks g := by simp [projectedAttacks,hs]
  intro i
  obtain ⟨j,hj⟩ := exists_ne (g i)
  let B := Finset.univ.filter (fun l => g l=j)
  have hB : B ∈ domainAttacks g := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,j,fun l hl => (Finset.mem_filter.mp hl).2⟩
  refine ⟨B,⟨by rwa [hp],?_⟩,?_⟩
  · intro D hD hBD
    rw [hp] at hD
    obtain ⟨j',hj'⟩ := (Finset.mem_filter.mp hD).2
    obtain ⟨l,hl⟩ := hg j
    have hlB : l ∈ B := by simp [B,hl]
    have he : j=j' := hl.symm.trans (hj' l (hBD hlB))
    intro t ht
    simp [B,hj' t ht,he]
  · simp [B,Ne.symm hj]

theorem failure_domain_optimum (g : ι → κ) (hg : Function.Surjective g) :
    IsLeast {v | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
      v=(domainAttacks g).sup' (domainAttacks_nonempty g) (fun C => ∑ i ∈ C, w i)}
      (1/(Fintype.card κ : ℝ)) := by
  have hh := failure_domain_game g hg
  have he : {v | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
      v=(domainAttacks g).sup' (domainAttacks_nonempty g) (fun C => ∑ i ∈ C, w i)} =
      {v | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
      v=gameUpper (fun j i => if g i=j then 1 else 0) w} := by
    ext v
    constructor <;> rintro ⟨w,hw,hs,hv⟩
    · exact ⟨w,hw,hs,hv.trans (domain_removable_weight g w hw)⟩
    · exact ⟨w,hw,hs,hv.trans (domain_removable_weight g w hw).symm⟩
  rwa [he]

end
end EvidenceFusion
