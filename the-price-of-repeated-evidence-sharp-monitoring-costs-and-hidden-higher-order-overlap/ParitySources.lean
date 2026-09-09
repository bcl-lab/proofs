import ParityIncidence
import WeightedGammaAttainment
import CappedReadBound

open OverlapReconstruction ParityIncidence MeasureTheory Set
open scoped BigOperators ENNReal

namespace RepeatedEvidenceProbability

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := cubeFintype n; inferInstanceAs (Fintype (Bool × Cube n))

def cubeAt : (n : ℕ) → Cube n → Fin n → Bool
  | 0, _, i => Fin.elim0 i
  | n+1, x, i => Fin.cases x.1 (fun j => cubeAt n x.2 j) i

def cubeExtends (n : ℕ) (R x : Cube n) : Prop :=
  ∀ i, cubeAt n R i = true → cubeAt n x i = true

instance cubeExtendsDecidable (n : ℕ) (R x : Cube n) : Decidable (cubeExtends n R x) :=
  inferInstanceAs (Decidable (∀ i, cubeAt n R i = true → cubeAt n x i = true))

theorem cubeExtends_succ (n : ℕ) (r b : Bool) (R x : Cube n) :
    cubeExtends (n+1) (r,R) (b,x) ↔ (r = true → b = true) ∧ cubeExtends n R x := by
  simp only [cubeExtends,Fin.forall_fin_succ,cubeAt,Fin.cases_zero,Fin.cases_succ]

theorem cubeAt_full (n : ℕ) (i : Fin n) : cubeAt n (full n) i = true := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ ?_ i
    · rfl
    · exact ih

theorem cube_degree_sum (n : ℕ) (x : Cube n) :
    (∑ i : Fin n, if cubeAt n x i = true then 1 else 0 : ℕ) = degree n x := by
  induction n with
  | zero => simp [degree]
  | succ n ih =>
    rcases x with ⟨b,x⟩
    rw [Fin.sum_univ_succ]
    cases b <;> simp [cubeAt,degree,ih]

/-- The recursive incidence transform equals an actual finite sum over
all source patterns satisfying the intersection query. -/
theorem zeta_eq_pattern_sum (n : ℕ) (f : Cube n → ℤ) (R : Cube n) :
    zeta n f R = ∑ x : Cube n, if cubeExtends n R x then f x else 0 := by
  induction n with
  | zero =>
    cases R
    simp only [zeta,cubeExtends,Fin.isEmpty,forall_const,IsEmpty.forall_iff,if_true]
    change f () = ∑ x : Unit, f x
    simp
  | succ n ih =>
    rcases R with ⟨r,R⟩
    change _ = ∑ x : Bool × Cube n, if cubeExtends (n+1) (r,R) x then f x else 0
    rw [Fintype.sum_prod_type]
    cases r <;> simp only [zeta,Bool.false_eq_true,if_false,if_true]
    · rw [ih]
      simp only [Fintype.sum_bool,cubeExtends_succ,Bool.false_eq_true,false_implies,true_and]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> ring
    · rw [ih]
      simp [Fintype.sum_bool,cubeExtends_succ]

/-- Every integer multiplicity is realized by that many distinct sources. -/
def ParitySource (n : ℕ) (b : Bool) : Type :=
  Σ x : Cube n, Fin ((multiplicity n 0 b x).toNat)

instance paritySourceFintype (n : ℕ) (b : Bool) : Fintype (ParitySource n b) :=
  inferInstanceAs (Fintype (Σ x : Cube n, Fin ((multiplicity n 0 b x).toNat)))

def parityUses (n : ℕ) (b : Bool) (v : ParitySource n b) (i : Fin n) : Prop :=
  cubeAt n v.1 i = true

instance parityUsesDecidable (n : ℕ) (b : Bool) : DecidableRel (parityUses n b) :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

noncomputable def parityOverlap (n : ℕ) (b : Bool) (R : Cube n) : ℕ :=
  ∑ v : ParitySource n b, if cubeExtends n R v.1 then 1 else 0

theorem paritySource_weight_sum (n : ℕ) (b : Bool) (f : Cube n → ℤ) :
    (∑ v : ParitySource n b, f v.1) = ∑ x : Cube n, multiplicity n 0 b x * f x := by
  change (∑ v : (Σ x : Cube n, Fin ((multiplicity n 0 b x).toNat)), f v.1) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  simp [Int.toNat_of_nonneg (multiplicity_nonnegative n 0 b x)]

theorem parityOverlap_eq_zeta (n : ℕ) (b : Bool) (R : Cube n) :
    (parityOverlap n b R : ℤ) = zeta n (multiplicity n 0 b) R := by
  classical
  unfold parityOverlap
  rw [zeta_eq_pattern_sum]
  push_cast
  calc
    _ = ∑ x : Cube n, multiplicity n 0 b x * (if cubeExtends n R x then (1:ℤ) else 0) :=
      paritySource_weight_sum n b (fun x => if cubeExtends n R x then 1 else 0)
    _ = _ := ?_
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : cubeExtends n R x
  · simp [hx]
  · simp [hx]

theorem paritySource_intersections (m : ℕ) (b : Bool) (R : Cube m)
    (hR : degree m R + 2 ≤ m) :
    parityOverlap m b R = (m+degree m R)*2^(m-degree m R-2) := by
  have h := parityOverlap_eq_zeta m b R
  rw [all_intersection_counts m R hR b] at h
  exact_mod_cast h

def singletonCube : (n : ℕ) → Fin n → Cube n
  | 0, i => Fin.elim0 i
  | n+1, i => Fin.cases (true,empty n) (fun j => (false,singletonCube n j)) i

theorem cubeAt_empty (n : ℕ) (i : Fin n) : cubeAt n (empty n) i = false := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ ?_ i
    · rfl
    · exact ih

theorem cubeExtends_empty (n : ℕ) (x : Cube n) : cubeExtends n (empty n) x := by
  intro i hi
  simp [cubeAt_empty] at hi

theorem cubeExtends_singleton (n : ℕ) (i : Fin n) (x : Cube n) :
    cubeExtends n (singletonCube n i) x ↔ cubeAt n x i = true := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases x with ⟨b,x⟩
    refine Fin.cases ?_ ?_ i
    · simp [singletonCube,cubeExtends_succ,cubeExtends_empty,cubeAt]
    · intro j
      simpa [singletonCube,cubeExtends_succ,cubeAt] using ih j x

theorem singletonCube_degree (n : ℕ) (i : Fin n) : degree n (singletonCube n i) = 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ ?_ i
    · simp [singletonCube,degree,degree_empty]
    · intro j
      simpa [singletonCube,degree] using ih j

theorem paritySource_union_card (m : ℕ) (hm : 2 ≤ m) (b : Bool) :
    Fintype.card (ParitySource m b) = m*2^(m-2) := by
  have h := paritySource_intersections m b (empty m) (by simpa [degree_empty] using hm)
  simpa [parityOverlap,cubeExtends_empty,degree_empty] using h

theorem paritySource_read_sum (m : ℕ) (b : Bool) (v : ParitySource m b) :
    (∑ i : Fin m, if parityUses m b v i then (1:ℝ) else 0) = degree m v.1 := by
  have h := cube_degree_sum m v.1
  unfold parityUses
  exact_mod_cast h

theorem paritySource_B_read_lt (m : ℕ) (v : ParitySource m (!(fullParity m))) :
    degree m v.1 < m := by
  apply opposite_parity_max_read m v.1
  intro h
  have hv := v.2.isLt
  simp [h] at hv

noncomputable def paritySourceA_full (m : ℕ) (hm : 0 < m) : ParitySource m (fullParity m) :=
  ⟨full m,⟨0,by rw [(full_multiplicity m 0).1]; simpa using hm⟩⟩

theorem paritySourceA_full_uses (m : ℕ) (hm : 0 < m) (i : Fin m) :
    parityUses m (fullParity m) (paritySourceA_full m hm) i := cubeAt_full m i

end RepeatedEvidenceProbability
