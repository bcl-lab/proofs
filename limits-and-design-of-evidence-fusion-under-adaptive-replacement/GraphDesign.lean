import FamilyDesign
import Mathlib.Combinatorics.SimpleGraph.Clique

open scoped BigOperators
open Finset Set
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvidenceFusion
noncomputable section
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Nonempty ι] [Nonempty κ]

def retainedCoefficient (B : κ → ι → ℝ) : ℝ :=
  1-sInf {v | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧ v=gameUpper B w}

theorem retained_fractional_cover_identity (B : κ → ι → ℝ)
    (hB : ∀ j i, 0 ≤ B j i) (hcover : ∀ i, ∃ j, 0 < B j i) :
    retainedCoefficient B=1-1/sInf (fractionalCoverValues B) := by
  obtain ⟨r,w,hr,hw,hs,he,hmin,hcovermin⟩ := fractional_cover_duality B hB hcover
  have hgame : IsLeast {v | ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i=1) ∧
      v=gameUpper B w} r := by
    constructor
    · exact ⟨w,hw,hs,he.symm⟩
    · rintro v ⟨w,hw,hs,rfl⟩
      exact hmin w hw hs
  rw [retainedCoefficient,hgame.csInf_eq,hcovermin.csInf_eq]
  simp

def graphAttackIndex (G : SimpleGraph ι) := {C : Finset ι // G.IsIndepSet (C : Set ι)}

noncomputable instance graphAttackIndex_fintype (G : SimpleGraph ι) : Fintype (graphAttackIndex G) := by
  classical
  unfold graphAttackIndex
  infer_instance

instance graphAttackIndex_nonempty (G : SimpleGraph ι) : Nonempty (graphAttackIndex G) := by
  refine ⟨⟨∅,?_⟩⟩
  rw [SimpleGraph.isIndepSet_iff]
  simp

def graphIncidence (G : SimpleGraph ι) (C : graphAttackIndex G) (i : ι) : ℝ :=
  if i ∈ C.val then 1 else 0

/-- The standard fractional-coloring covering-program value. -/
def fractionalChromatic (G : SimpleGraph ι) : ℝ :=
  sInf (fractionalCoverValues (graphIncidence G))

theorem graph_retention_identity (G : SimpleGraph ι) :
    retainedCoefficient (graphIncidence G)=1-1/fractionalChromatic G := by
  classical
  apply retained_fractional_cover_identity
  · intro C i
    unfold graphIncidence
    split_ifs <;> norm_num
  · intro i
    have hi : G.IsIndepSet (({i} : Finset ι) : Set ι) := by
      rw [SimpleGraph.isIndepSet_iff]
      simp
    exact ⟨⟨{i},hi⟩,by simp [graphIncidence]⟩

end
end EvidenceFusion
