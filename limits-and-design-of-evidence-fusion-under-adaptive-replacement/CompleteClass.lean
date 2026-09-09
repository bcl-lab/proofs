import Probability
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Convex.Combination
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic.Choose

open scoped BigOperators
open Finset Set MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace EvidenceFusion
noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def Compatible (A : Finset (Finset ι)) (x y : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧
    ∃ C ∈ A, ∀ i, i ∉ C → y i = x i

def FiniteRobustValid (A : Finset (Finset ι)) (F : (ι → ℝ) → ℝ) : Prop :=
  ∀ (Ω : Type) [Fintype Ω] (p : Ω → ℝ) (X Y : Ω → ι → ℝ),
    (∀ ω, 0 ≤ p ω) → (∑ ω, p ω = 1) →
    (∀ ω, Compatible A (X ω) (Y ω)) →
    (∀ i, ∑ ω, p ω * X ω i ≤ 1) →
    ∑ ω, p ω * F (Y ω) ≤ 1

def momentPoint (x : ι → ℝ) (r : ℝ) : Option ι → ℝ :=
  fun j => j.elim r x

def momentSet (A : Finset (Finset ι)) (F : (ι → ℝ) → ℝ) : Set (Option ι → ℝ) :=
  {z | ∃ x y, Compatible A x y ∧ z = momentPoint x (F y)}

def violationRegion : Set (Option ι → ℝ) :=
  {z | (∀ i, z (some i) < 1) ∧ 1 < z none}

theorem violationRegion_convex : Convex ℝ (violationRegion (ι := ι)) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change a * x (some i) + b * y (some i) < 1
    have hxi := hx.1 i
    have hyi := hy.1 i
    have h1 := mul_nonneg ha (sub_pos.mpr hxi).le
    have h2 := mul_nonneg hb (sub_pos.mpr hyi).le
    rcases lt_or_eq_of_le ha with ha' | rfl
    · have := mul_pos ha' (sub_pos.mpr hxi)
      nlinarith
    · have : b = 1 := by linarith
      simpa [this] using hyi
  · change 1 < a * x none + b * y none
    have h1 := mul_nonneg ha (sub_pos.mpr hx.2).le
    have h2 := mul_nonneg hb (sub_pos.mpr hy.2).le
    rcases lt_or_eq_of_le ha with ha' | rfl
    · have := mul_pos ha' (sub_pos.mpr hx.2)
      nlinarith [hx.2, hy.2]
    · have : b = 1 := by linarith
      simpa [this] using hy.2

theorem violationRegion_open : IsOpen (violationRegion (ι := ι)) := by
  have he : violationRegion (ι := ι) =
      (⋂ i : ι, {z : Option ι → ℝ | z (some i) < 1}) ∩
      {z : Option ι → ℝ | 1 < z none} := by
    ext z
    simp [violationRegion]
  rw [he]
  exact (isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_apply (some i)) continuous_const).inter
    (isOpen_lt continuous_const (continuous_apply none))

theorem valid_hull_disjoint (A : Finset (Finset ι)) (F : (ι → ℝ) → ℝ)
    (hvalid : FiniteRobustValid A F) :
    Disjoint violationRegion (convexHull ℝ (momentSet A F)) := by
  apply Set.disjoint_left.mpr
  intro z hz hzh
  obtain ⟨Ω, fΩ, p, Z, hp, hp1, hZ, he⟩ := mem_convexHull_iff_exists_fintype.mp hzh
  letI : Fintype Ω := fΩ
  choose X Y hcomp hpoint using hZ
  have hcoord (j : Option ι) : (∑ ω, p ω * momentPoint (X ω) (F (Y ω)) j) = z j := by
    have hh := congrFun he j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hpoint] using hh
  have hmean (i : ι) : ∑ ω, p ω * X ω i ≤ 1 := by
    have hh := hcoord (some i)
    simp only [momentPoint, Option.elim_some] at hh
    rw [hh]
    exact (hz.1 i).le
  have hf := hvalid Ω p X Y hp hp1 hcomp hmean
  have hh := hcoord none
  simp only [momentPoint, Option.elim_none] at hh
  linarith [hz.2]

theorem linear_moment_expansion (L : (Option ι → ℝ) →L[ℝ] ℝ)
    (x : ι → ℝ) (r : ℝ) :
    L (momentPoint x r) =
      r * L (Pi.single none 1) + ∑ i, x i * L (Pi.single (some i) 1) := by
  have he (z : Option ι → ℝ) : z = ∑ j, z j • (Pi.single j (1 : ℝ) : Option ι → ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  rw [he (momentPoint x r), map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Fintype.sum_option]
  simp only [momentPoint, Option.elim_none, Option.elim_some]

/-- The complete affine converse, obtained by finite-dimensional separation.
The finite-law validity premise quantifies over every finite probability law. -/
theorem complete_affine_converse (A : Finset (Finset ι)) (hA : A.Nonempty)
    (F : (ι → ℝ) → ℝ) (hFn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y)
    (hvalid : FiniteRobustValid A F) :
    ∃ (a : ℝ) (w : ι → ℝ), 0 ≤ a ∧ (∀ i, 0 ≤ w i) ∧
      a + ∑ i, w i = 1 ∧
      ∀ x y, Compatible A x y → F y ≤ a + ∑ i, w i * x i := by
  obtain ⟨L, u, hopen, hhull⟩ := geometric_hahn_banach_open
    (violationRegion_convex (ι := ι)) violationRegion_open
    (convex_convexHull ℝ (momentSet A F)) (valid_hull_disjoint A F hvalid)
  let c := L (Pi.single none 1)
  let v : ι → ℝ := fun i => L (Pi.single (some i) 1)
  have hexp (x : ι → ℝ) (r : ℝ) :
      L (momentPoint x r) = c*r + ∑ i, v i*x i := by
    rw [linear_moment_expansion]
    dsimp [c, v]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  have hzero : Compatible A (0 : ι → ℝ) 0 := by
    obtain ⟨C,hC⟩ := hA
    exact ⟨by simp, by simp, C,hC,by simp⟩
  have hz : u ≤ c * F 0 := by
    have hh := hhull (momentPoint 0 (F 0))
      (subset_convexHull ℝ (momentSet A F) ⟨0,0,hzero,rfl⟩)
    simpa [hexp] using hh
  have hF0 : 0 ≤ F 0 := hFn 0 (by simp)
  have hc : c < 0 := by
    have hh := hopen (momentPoint 0 (F 0 + 2))
      (show momentPoint (0 : ι → ℝ) (F 0 + 2) ∈ violationRegion by
        constructor <;> simp [momentPoint] <;> linarith)
    rw [hexp] at hh
    simp only [Pi.zero_apply, mul_zero, sum_const_zero, add_zero] at hh
    nlinarith
  have hv (i : ι) : 0 ≤ v i := by
    have hs : -v i ≤ 0 := slope_comparison (a := c*2) (b := u) (w := -v i) (v := 0) (by
      intro t ht
      have hh := hopen (momentPoint (Pi.single i (-t)) 2) (by
        constructor
        · intro j
          simp only [momentPoint, Option.elim_some, Pi.single_apply]
          split_ifs <;> linarith
        · norm_num [momentPoint])
      rw [hexp] at hh
      simp [Pi.single_apply] at hh
      nlinarith)
    linarith
  have hsum : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ => hv i
  have hboundary : c + ∑ i, v i ≤ u := by
    by_contra hn
    have hgap : 0 < c + (∑ i, v i) - u := sub_pos.mpr (lt_of_not_ge hn)
    have hd : 0 < (∑ i, v i) - c := by linarith
    let e := (c + (∑ i, v i) - u) / (2*((∑ i, v i)-c))
    have he : 0 < e := div_pos hgap (by positivity)
    have hh := hopen (momentPoint (fun _ => 1-e) (1+e)) (by
      constructor
      · intro i; change 1-e < 1; linarith
      · change 1 < 1+e; linarith)
    rw [hexp, ← Finset.sum_mul] at hh
    have heq : e*(2*((∑ i, v i)-c)) = c+(∑ i,v i)-u := by
      dsimp [e]
      field_simp [ne_of_gt hd]
    nlinarith
  let w : ι → ℝ := fun i => v i / (-c)
  let a : ℝ := 1 - ∑ i, w i
  have hcpos : 0 < -c := neg_pos.mpr hc
  have hw (i : ι) : 0 ≤ w i := div_nonneg (hv i) hcpos.le
  have hwsum : ∑ i, w i = (∑ i, v i)/(-c) := by
    simp only [w, Finset.sum_div]
  have hunonpos : u ≤ 0 := hz.trans (mul_nonpos_of_nonpos_of_nonneg hc.le hF0)
  have ha : 0 ≤ a := by
    dsimp [a]
    rw [hwsum]
    have hh : (∑ i, v i)/(-c) ≤ 1 := (div_le_iff₀ hcpos).mpr (by linarith)
    linarith
  refine ⟨a,w,ha,hw,by dsimp [a]; ring,?_⟩
  intro x y hxy
  have hh := hhull (momentPoint x (F y))
    (subset_convexHull ℝ (momentSet A F) ⟨x,y,hxy,rfl⟩)
  rw [hexp] at hh
  have he : (∑ i, w i*x i) * (-c) = ∑ i, v i*x i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w]
    field_simp [hc.ne]
  apply (mul_le_mul_right hcpos).mp
  have hae : a * (-c) = -c - ∑ i, v i := by
    dsimp [a]
    rw [hwsum]
    field_simp [hc.ne]
  nlinarith

theorem complete_class_finite (A : Finset (Finset ι)) (hA : A.Nonempty)
    (F : (ι → ℝ) → ℝ) (hFn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y) :
    FiniteRobustValid A F ↔
      ∃ (a : ℝ) (w : ι → ℝ), 0 ≤ a ∧ (∀ i, 0 ≤ w i) ∧
        a + ∑ i, w i = 1 ∧
        ∀ y, (∀ i, 0 ≤ y i) → F y ≤ robustAffine a w y A hA := by
  constructor
  · intro hv
    obtain ⟨a,w,ha,hw,hn,hdom⟩ := complete_affine_converse A hA F hFn hv
    refine ⟨a,w,ha,hw,hn,?_⟩
    intro y hy
    unfold robustAffine
    apply (sub_le_iff_le_add').mp
    apply Finset.le_inf'
    intro C hC
    let x : ι → ℝ := fun i => if i ∈ C then 0 else y i
    have hxy : Compatible A x y := by
      refine ⟨?_,hy,C,hC,?_⟩
      · intro i; dsimp [x]; split_ifs; exact le_rfl; exact hy i
      · intro i hi; simp [x,hi]
    have hh := hdom x y hxy
    have he : (∑ i, w i*x i) = keptSum w y C := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [x]
      split_ifs <;> simp_all
    rw [he] at hh
    linarith
  · rintro ⟨a,w,ha,hw,hn,hdom⟩ Ω fΩ p X Y hp hp1 hcomp hmean
    apply finite_probability_validity p (fun ω => F (Y ω)) X a w hp hp1 hw hn hmean
    intro ω
    obtain ⟨hx,hy,C,hC,hclean⟩ := hcomp ω
    exact (hdom (Y ω) hy).trans
      (robustAffine_le_clean a w (X ω) (Y ω) A hA C hC hw hx hclean)

/-- Validity for all compatible random vectors on arbitrary probability spaces.
The statistic's measurability is explicit, and its integrability is a conclusion. -/
def ProbabilityRobustValid (A : Finset (Finset ι)) (F : (ι → ℝ) → ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ι → ℝ),
    (∀ i, Integrable (fun ω => X ω i) μ) →
    (∀ i, (∫ ω, X ω i ∂μ) ≤ 1) →
    (∀ᵐ ω ∂μ, Compatible A (X ω) (Y ω)) →
    AEStronglyMeasurable (fun ω => F (Y ω)) μ →
    Integrable (fun ω => F (Y ω)) μ ∧ (∫ ω, F (Y ω) ∂μ) ≤ 1

theorem probability_valid_implies_finite (A : Finset (Finset ι))
    (F : (ι → ℝ) → ℝ) (hv : ProbabilityRobustValid A F) :
    FiniteRobustValid A F := by
  intro Ω fΩ p X Y hp hp1 hcomp hmean
  letI : MeasurableSpace Ω := ⊤
  let μ : Measure Ω := ∑ ω, ENNReal.ofReal (p ω) • Measure.dirac ω
  have hmass : ∑ ω, ENNReal.ofReal (p ω) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => hp ω), hp1]
    simp
  letI : IsProbabilityMeasure μ := ⟨by
    simp [μ, Measure.finset_sum_apply, hmass]⟩
  have hint (f : Ω → ℝ) : (∫ ω, f ω ∂μ) = ∑ ω, p ω * f ω := by
    rw [integral_fintype f Integrable.of_finite]
    apply Finset.sum_congr rfl
    intro ω _
    have hm : μ.real {ω} = p ω := by
      have hm' : μ {ω} = ENNReal.ofReal (p ω) := by
        rw [show μ = ∑ j, ENNReal.ofReal (p j) • Measure.dirac j from rfl,
          Measure.finset_sum_apply]
        rw [Finset.sum_eq_single ω]
        · simp [Measure.smul_apply, Measure.dirac_apply_of_mem]
        · intro j _ hjo
          simp [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_not_mem, hjo]
        · simp
      change (μ {ω}).toReal = p ω
      rw [hm',ENNReal.toReal_ofReal (hp ω)]
    simp [hm]
  have hh := hv Ω μ X Y (fun _ => Integrable.of_finite)
    (fun i => by rw [hint]; exact hmean i)
    (Filter.Eventually.of_forall hcomp) (Integrable.of_finite.aestronglyMeasurable)
  rw [hint] at hh
  exact hh.2

/-- The full complete-class equivalence on arbitrary probability spaces.
No unproved representation theorem is included among the assumptions. -/
theorem complete_class_probability (A : Finset (Finset ι)) (hA : A.Nonempty)
    (F : (ι → ℝ) → ℝ) (hFn : ∀ y, (∀ i, 0 ≤ y i) → 0 ≤ F y) :
    ProbabilityRobustValid A F ↔
      ∃ (a : ℝ) (w : ι → ℝ), 0 ≤ a ∧ (∀ i, 0 ≤ w i) ∧
        a + ∑ i, w i = 1 ∧
        ∀ y, (∀ i, 0 ≤ y i) → F y ≤ robustAffine a w y A hA := by
  constructor
  · intro hv
    exact (complete_class_finite A hA F hFn).mp
      (probability_valid_implies_finite A F hv)
  · rintro ⟨a,w,ha,hw,hn,hdom⟩ Ω mΩ μ hμ X Y hX hmean hcomp hmeas
    apply arbitrary_probability_validity μ (fun ω => F (Y ω)) X a w
      hX hmean hw hn hmeas
    · filter_upwards [hcomp] with ω hω
      exact hFn (Y ω) hω.2.1
    · filter_upwards [hcomp] with ω hω
      obtain ⟨hx,hy,C,hC,hclean⟩ := hω
      exact (hdom (Y ω) hy).trans
        (robustAffine_le_clean a w (X ω) (Y ω) A hA C hC hw hx hclean)

end
end EvidenceFusion
