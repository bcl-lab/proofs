import Fusion.Flow
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi

namespace Fusion
open Finset

/-- Every nonempty finite completion problem has attained extrema for an
    arbitrary real-valued target. This statement concerns binary completions. -/
theorem finite_binary_extrema {ι : Type*} [Fintype ι]
    (P : (ι → Bool) → Prop) (cost : (ι → Bool) → ℝ) (h : ∃ y, P y) :
    ∃ lo hi, P lo ∧ P hi ∧ ∀ y, P y → cost lo ≤ cost y ∧ cost y ≤ cost hi := by
  classical
  let candidates : Finset (ι → Bool) := univ.filter P
  have hc : candidates.Nonempty := by
    obtain ⟨y,hy⟩ := h
    exact ⟨y,mem_filter.mpr ⟨mem_univ y,hy⟩⟩
  obtain ⟨lo,hlo,hmin⟩ := exists_min_image candidates cost hc
  obtain ⟨hi,hhi,hmax⟩ := exists_max_image candidates cost hc
  refine ⟨lo,hi,(mem_filter.mp hlo).2,(mem_filter.mp hhi).2,?_⟩
  intro y hy
  exact ⟨hmin y (mem_filter.mpr ⟨mem_univ y,hy⟩),
    hmax y (mem_filter.mpr ⟨mem_univ y,hy⟩)⟩

def boolToInt {ι : Type*} (y : ι → Bool) : ι → ℤ := fun i => if y i then 1 else 0

/-- Every integer vector known to be binary has a Boolean encoding. -/
theorem binary_encoding {ι : Type*} (y : ι → ℤ) (h : ∀ i, y i=0 ∨ y i=1) :
    ∃ b : ι → Bool, boolToInt b = y := by
  refine ⟨fun i => decide (y i = 1),?_⟩
  funext i
  rcases h i with hi | hi <;> simp [boolToInt,hi]

theorem binary_integer_extrema {ι : Type*} [Fintype ι]
    (P : (ι → ℤ) → Prop) (cost : (ι → ℤ) → ℝ)
    (hb : ∀ y, P y → ∀ i, y i=0 ∨ y i=1) (hne : ∃ y, P y) :
    ∃ lo hi, P lo ∧ P hi ∧ ∀ y, P y → cost lo ≤ cost y ∧ cost y ≤ cost hi := by
  have hne' : ∃ b, P (boolToInt b) := by
    obtain ⟨y,hy⟩ := hne
    obtain ⟨b,rfl⟩ := binary_encoding y (hb y hy)
    exact ⟨b,hy⟩
  obtain ⟨lo,hi,hlo,hhi,he⟩ := finite_binary_extrema
    (fun b => P (boolToInt b)) (fun b => cost (boolToInt b)) hne'
  refine ⟨boolToInt lo,boolToInt hi,hlo,hhi,?_⟩
  intro y hy
  obtain ⟨b,rfl⟩ := binary_encoding y (hb y hy)
  exact he b hy

/-- Sharp endpoints are attained on the integer flow network and coincide
    with the completion endpoints, including intervals and reviewed labels.
    Continuous relaxation integrality is a separate obligation. -/
theorem integer_flow_endpoints {n h k : ℕ} (d : CountData n h k)
    (cost : (Fin n → ℤ) → ℝ) (hne : ∃ y, CountFeasible d y) :
    ∃ lo hi slo tlo shi thi,
      CountFeasible d lo ∧ CountFeasible d hi ∧
      FlowFeasible d lo slo tlo ∧ FlowFeasible d hi shi thi ∧
      (∀ y, CountFeasible d y → cost lo ≤ cost y ∧ cost y ≤ cost hi) ∧
      (∀ y s t, FlowFeasible d y s t → cost lo ≤ cost y ∧ cost y ≤ cost hi) := by
  obtain ⟨lo,hi,hlo,hhi,he⟩ := binary_integer_extrema (CountFeasible d) cost
    (fun _ hy => hy.1) hne
  obtain ⟨slo,tlo,hflo⟩ := (count_flow_correspondence d lo).mp hlo
  obtain ⟨shi,thi,hfhi⟩ := (count_flow_correspondence d hi).mp hhi
  refine ⟨lo,hi,slo,tlo,shi,thi,hlo,hhi,hflo,hfhi,he,?_⟩
  intro y s t hy
  exact he y ((count_flow_correspondence d y).mpr ⟨s,t,hy⟩)

end Fusion
