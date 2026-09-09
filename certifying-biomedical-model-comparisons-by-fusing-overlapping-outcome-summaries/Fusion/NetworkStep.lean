import Fusion.NetworkRounding

namespace FusionNetwork
open Finset
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem fractional_strict_bounds (x : ℝ) (hx : ¬IsInt x) :
    (Int.floor x : ℝ) < x ∧ x < (Int.ceil x : ℝ) := by
  constructor
  · have h := Int.floor_le x
    have hn : (Int.floor x : ℝ) ≠ x := fun he => hx ⟨Int.floor x,he⟩
    exact lt_of_le_of_ne h hn
  · have h := Int.le_ceil x
    have hn : x ≠ (Int.ceil x : ℝ) := fun he => hx ⟨Int.ceil x,he.symm⟩
    exact lt_of_le_of_ne h hn

noncomputable def stepLimit (x d : ℝ) : ℝ :=
  if 0 < d then ((Int.ceil x : ℝ)-x)/d else (x-(Int.floor x : ℝ))/(-d)

theorem stepLimit_pos (x d : ℝ) (hx : ¬IsInt x) (hd : d ≠ 0) : 0 < stepLimit x d := by
  obtain ⟨hl,hu⟩ := fractional_strict_bounds x hx
  unfold stepLimit
  split_ifs with hp
  · exact div_pos (sub_pos.mpr hu) hp
  · have hn : 0 < -d := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hd)
    exact div_pos (sub_pos.mpr hl) hn

theorem step_inside (x d t : ℝ) (hd : d ≠ 0) (ht : 0 ≤ t) (hlim : t ≤ stepLimit x d) :
    (Int.floor x : ℝ) ≤ x+t*d ∧ x+t*d ≤ (Int.ceil x : ℝ) := by
  have hl := Int.floor_le x
  have hu := Int.le_ceil x
  unfold stepLimit at hlim
  split_ifs at hlim with hp
  · have hb := (le_div_iff₀ hp).mp hlim
    have htpos := mul_nonneg ht hp.le
    constructor <;> linarith
  · have hn : 0 < -d := neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hd)
    have hb := (le_div_iff₀ hn).mp hlim
    have htneg := mul_nonpos_of_nonneg_of_nonpos ht (by linarith : d ≤ 0)
    constructor <;> linarith

theorem step_hits_integer (x d : ℝ) (hd : d ≠ 0) : IsInt (x+stepLimit x d*d) := by
  unfold stepLimit
  split_ifs with hp
  · refine ⟨Int.ceil x,?_⟩
    rw [div_mul_cancel₀ _ hd]
    ring
  · refine ⟨Int.floor x,?_⟩
    have hc := div_mul_cancel₀ (x-(Int.floor x : ℝ)) (neg_ne_zero.mpr hd)
    nlinarith

noncomputable def fractionalSet (x : E → ℝ) : Finset E := by
  classical
  exact univ.filter (fun e => ¬IsInt (x e))

theorem mem_fractionalSet (x : E → ℝ) (e : E) : e ∈ fractionalSet x ↔ ¬IsInt (x e) := by
  classical
  simp [fractionalSet]

/-- One nonincreasing-cost step preserves all integer bounds and balances,
    keeps every integer coordinate integer, and makes at least one new
    coordinate integer. -/
theorem rounding_step (src dst : E → V) (lower upper : E → ℤ) (x cost : E → ℝ)
    (hx : ∀ e, (lower e : ℝ) ≤ x e ∧ x e ≤ (upper e : ℝ))
    (hb : ∀ v, IsInt (balance src dst x v)) (hf : ∃ e, ¬IsInt (x e)) :
    ∃ y : E → ℝ,
      (∀ e, (lower e : ℝ) ≤ y e ∧ y e ≤ (upper e : ℝ)) ∧
      (∀ v, balance src dst y v = balance src dst x v) ∧
      (∑ e, cost e*y e) ≤ ∑ e, cost e*x e ∧
      (fractionalSet y).card < (fractionalSet x).card := by
  classical
  obtain ⟨d,hdne,hds,hdb,hdcost⟩ := improving_direction src dst x cost hb hf
  let S : Finset E := univ.filter (fun e => d e ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨e,he⟩ := hdne
    exact ⟨e,mem_filter.mpr ⟨mem_univ e,he⟩⟩
  obtain ⟨e0,he0,hmin⟩ := exists_min_image S (fun e => stepLimit (x e) (d e)) hS
  have hd0 : d e0 ≠ 0 := (mem_filter.mp he0).2
  have hxf (e : E) (he : d e ≠ 0) : ¬IsInt (x e) := fun hi => he (hds e hi)
  let t := stepLimit (x e0) (d e0)
  have ht : 0 < t := stepLimit_pos _ _ (hxf e0 hd0) hd0
  let y : E → ℝ := fun e => x e+t*d e
  have hyp (e : E) (hi : IsInt (x e)) : IsInt (y e) := by
    simpa [y,hds e hi] using hi
  have hnew : IsInt (y e0) := step_hits_integer _ _ hd0
  refine ⟨y,?_,?_,?_,?_⟩
  · intro e
    by_cases hde : d e = 0
    · simpa [y,hde] using hx e
    · have hs := step_inside (x e) (d e) t hde ht.le
        (hmin e (mem_filter.mpr ⟨mem_univ e,hde⟩))
      have hlo : (lower e : ℝ) ≤ (Int.floor (x e) : ℝ) := by
        exact_mod_cast (Int.le_floor.mpr (hx e).1)
      have hup : (Int.ceil (x e) : ℝ) ≤ (upper e : ℝ) := by
        exact_mod_cast (Int.ceil_le.mpr (hx e).2)
      exact ⟨hlo.trans hs.1,hs.2.trans hup⟩
  · intro v
    change balance src dst (fun e => x e+t*d e) v = _
    rw [balance_add,balance_scale,hdb]
    ring
  · have heq : (∑ e, cost e*y e) = (∑ e, cost e*x e) + t*(∑ e, cost e*d e) := by
      simp only [y,mul_add,sum_add_distrib,mul_sum]
      congr 1
      apply sum_congr rfl; intro e he; ring
    rw [heq]
    have hnon := mul_nonpos_of_nonneg_of_nonpos ht.le hdcost
    linarith
  · apply card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro e he
      apply (mem_fractionalSet x e).mpr
      intro hi
      exact (mem_fractionalSet y e).mp he (hyp e hi)
    · intro heq
      have hm : e0 ∈ fractionalSet x := (mem_fractionalSet x e0).mpr (hxf e0 hd0)
      rw [← heq] at hm
      exact (mem_fractionalSet y e0).mp hm hnew

/-- Finite descent in the number of noninteger coordinates proves rounding
    for arbitrary bounded networks, real costs, parallel arcs, and loops. -/
theorem round_flow (src dst : E → V) (lower upper : E → ℤ) (cost : E → ℝ) :
    ∀ x : E → ℝ,
      (∀ e, (lower e : ℝ) ≤ x e ∧ x e ≤ (upper e : ℝ)) →
      (∀ v, IsInt (balance src dst x v)) →
      ∃ y : E → ℝ, (∀ e, IsInt (y e)) ∧
        (∀ e, (lower e : ℝ) ≤ y e ∧ y e ≤ (upper e : ℝ)) ∧
        (∀ v, balance src dst y v = balance src dst x v) ∧
        (∑ e, cost e*y e) ≤ ∑ e, cost e*x e := by
  classical
  suffices aux : ∀ n : ℕ, ∀ x : E → ℝ, (fractionalSet x).card ≤ n →
      (∀ e, (lower e : ℝ) ≤ x e ∧ x e ≤ (upper e : ℝ)) →
      (∀ v, IsInt (balance src dst x v)) →
      ∃ y : E → ℝ, (∀ e, IsInt (y e)) ∧
        (∀ e, (lower e : ℝ) ≤ y e ∧ y e ≤ (upper e : ℝ)) ∧
        (∀ v, balance src dst y v = balance src dst x v) ∧
        (∑ e, cost e*y e) ≤ ∑ e, cost e*x e by
    intro x hx hb
    exact aux (fractionalSet x).card x le_rfl hx hb
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x hn hx hb
    by_cases hall : ∀ e, IsInt (x e)
    · exact ⟨x,hall,hx,fun _ => rfl,le_rfl⟩
    · obtain ⟨e,he⟩ := not_forall.mp hall
      obtain ⟨z,hz,hzb,hzc,hzf⟩ := rounding_step src dst lower upper x cost hx hb ⟨e,he⟩
      have hlt : (fractionalSet z).card < n := lt_of_lt_of_le hzf hn
      obtain ⟨y,hy,hyb,hyv,hyc⟩ := ih (fractionalSet z).card hlt z le_rfl hz
        (by intro v; rw [hzb v]; exact hb v)
      exact ⟨y,hy,hyb,fun v => (hyv v).trans (hzb v),hyc.trans hzc⟩

/-- Cost-nonincreasing integral rounding, with integer-valued output. -/
theorem real_flow_rounding (src dst : E → V) (lower upper : E → ℤ) (cost x : E → ℝ)
    (hx : ∀ e, (lower e : ℝ) ≤ x e ∧ x e ≤ (upper e : ℝ))
    (hb : ∀ v, IsInt (balance src dst x v)) :
    ∃ z : E → ℤ, (∀ e, lower e ≤ z e ∧ z e ≤ upper e) ∧
      (∀ v, balance src dst (fun e => (z e : ℝ)) v = balance src dst x v) ∧
      (∑ e, cost e*(z e : ℝ)) ≤ ∑ e, cost e*x e := by
  obtain ⟨y,hi,hy,hb',hc⟩ := round_flow src dst lower upper cost x hx hb
  choose z hz using hi
  have heq : (fun e => (z e : ℝ)) = y := funext hz
  refine ⟨z,?_,?_,?_⟩
  · intro e
    have he := hy e
    rw [← hz e] at he
    exact_mod_cast he
  · simpa only [heq] using hb'
  · simpa only [hz] using hc

end FusionNetwork
