import EvidenceFusion
import Mathlib.Order.CompleteLattice.Basic

open scoped BigOperators
open Finset
set_option autoImplicit false

namespace EvidenceFusion
noncomputable section
variable {ι α β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
  [CompleteLattice β]

/-- Completion envelopes in a complete lattice, so unbounded infima are meaningful. -/
def completionInf (k : ℕ) (f : (ι → α) → β) (x : ι → α) : β :=
  ⨅ y, ⨅ (_ : hamming x y ≤ k), f y

/-- Full nested-infimum identity, without compactness or attainment assumptions. -/
theorem completionInf_composition (f : (ι → α) → β) (x : ι → α) (k l : ℕ) :
    completionInf l (completionInf k f) x =
      completionInf (min (Fintype.card ι) (k+l)) f x := by
  unfold completionInf
  apply le_antisymm
  · refine le_iInf fun z => le_iInf fun hz => ?_
    have hz' : hamming x z ≤ min (Fintype.card ι) (l+k) := by
      simpa [Nat.add_comm] using hz
    obtain ⟨y,hxy,hyz⟩ := (hamming_ball_composition x z l k).mpr hz'
    exact iInf_le_of_le y (iInf_le_of_le hxy
      (iInf_le_of_le z (iInf_le _ hyz)))
  · refine le_iInf fun y => le_iInf fun hxy => le_iInf fun z => le_iInf fun hyz => ?_
    have hz : hamming x z ≤ min (Fintype.card ι) (k+l) := by
      simpa [Nat.add_comm] using (hamming_ball_composition x z l k).mp ⟨y,hxy,hyz⟩
    exact iInf_le_of_le z (iInf_le _ hz)

end
end EvidenceFusion
