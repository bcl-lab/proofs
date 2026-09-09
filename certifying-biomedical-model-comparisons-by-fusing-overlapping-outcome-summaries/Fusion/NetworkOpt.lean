import Fusion.NetworkStep
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

namespace FusionNetwork
open Finset
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def RealFeasible (src dst : E → V) (lower upper : E → ℤ) (supply : V → ℤ)
    (x : E → ℝ) : Prop :=
  (∀ e, (lower e : ℝ) ≤ x e ∧ x e ≤ (upper e : ℝ)) ∧
  ∀ v, balance src dst x v = (supply v : ℝ)

def IntegerFeasible (src dst : E → V) (lower upper : E → ℤ) (supply : V → ℤ)
    (z : E → ℤ) : Prop := RealFeasible src dst lower upper supply (fun e => (z e : ℝ))

theorem integer_bounds (src dst : E → V) (lower upper : E → ℤ) (supply : V → ℤ)
    (z : E → ℤ) (hz : IntegerFeasible src dst lower upper supply z) :
    ∀ e, lower e ≤ z e ∧ z e ≤ upper e := by
  intro e
  have hh := hz.1 e
  dsimp at hh
  exact_mod_cast hh

theorem round_feasible (src dst : E → V) (lower upper : E → ℤ) (supply : V → ℤ)
    (cost x : E → ℝ) (hx : RealFeasible src dst lower upper supply x) :
    ∃ z : E → ℤ, IntegerFeasible src dst lower upper supply z ∧
      (∑ e, cost e*(z e : ℝ)) ≤ ∑ e, cost e*x e := by
  obtain ⟨z,hz,hb,hc⟩ := real_flow_rounding src dst lower upper cost x hx.1
    (fun v => ⟨supply v,(hx.2 v).symm⟩)
  refine ⟨z,⟨?_,?_⟩,hc⟩
  · intro e; dsimp; exact_mod_cast hz e
  · intro v; exact (hb v).trans (hx.2 v)

/-- The bounded real-flow problem has an attained integral minimum. This
    is proved from rounding and a finite integer box, without assuming
    continuous optimization attainment or an integrality theorem. -/
theorem min_cost_integral (src dst : E → V) (lower upper : E → ℤ) (supply : V → ℤ)
    (cost : E → ℝ) (hne : ∃ x, RealFeasible src dst lower upper supply x) :
    ∃ z : E → ℤ, IntegerFeasible src dst lower upper supply z ∧
      ∀ x, RealFeasible src dst lower upper supply x →
        (∑ e, cost e*(z e : ℝ)) ≤ ∑ e, cost e*x e := by
  classical
  let candidates := (Fintype.piFinset fun e => Finset.Icc (lower e) (upper e)).filter
    (IntegerFeasible src dst lower upper supply)
  have hcand (z : E → ℤ) : z ∈ candidates ↔ IntegerFeasible src dst lower upper supply z := by
    simp only [candidates,mem_filter,Fintype.mem_piFinset,mem_Icc]
    exact ⟨fun h => h.2,fun h => ⟨integer_bounds src dst lower upper supply z h,h⟩⟩
  have hnonempty : candidates.Nonempty := by
    obtain ⟨x,hx⟩ := hne
    obtain ⟨z,hz,_⟩ := round_feasible src dst lower upper supply cost x hx
    exact ⟨z,(hcand z).mpr hz⟩
  obtain ⟨z,hz,hmin⟩ := exists_min_image candidates (fun z => ∑ e, cost e*(z e : ℝ)) hnonempty
  refine ⟨z,(hcand z).mp hz,?_⟩
  intro x hx
  obtain ⟨w,hw,hcost⟩ := round_feasible src dst lower upper supply cost x hx
  exact (hmin w ((hcand w).mpr hw)).trans hcost

/-- Both extrema of every nonempty bounded real-flow problem are attained
    by integral flows; minimization with the negated cost supplies the maximum. -/
theorem integral_flow_extrema (src dst : E → V) (lower upper : E → ℤ) (supply : V → ℤ)
    (cost : E → ℝ) (hne : ∃ x, RealFeasible src dst lower upper supply x) :
    ∃ lo hi : E → ℤ,
      IntegerFeasible src dst lower upper supply lo ∧
      IntegerFeasible src dst lower upper supply hi ∧
      ∀ x, RealFeasible src dst lower upper supply x →
        (∑ e, cost e*(lo e : ℝ)) ≤ (∑ e, cost e*x e) ∧
        (∑ e, cost e*x e) ≤ ∑ e, cost e*(hi e : ℝ) := by
  obtain ⟨lo,hlo,hmin⟩ := min_cost_integral src dst lower upper supply cost hne
  obtain ⟨hi,hhi,hmax⟩ := min_cost_integral src dst lower upper supply (fun e => -cost e) hne
  refine ⟨lo,hi,hlo,hhi,?_⟩
  intro x hx
  refine ⟨hmin x hx,?_⟩
  have h := hmax x hx
  simpa only [neg_mul,sum_neg_distrib,neg_le_neg_iff] using h

end FusionNetwork
