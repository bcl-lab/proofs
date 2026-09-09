import Fusion.TreeCounts

namespace FusionTree
open Finset Fusion

def labelObs (k : ℕ) (s : Leaf k × Bool) : Edge k → Bool := labels k (path k s)
def labelTarget (k : ℕ) (y : Edge k → Bool) : ℤ := ∑ e, coefficient k e * bit (y e)

theorem label_target_sign (k : ℕ) (s : Leaf k × Bool) :
    labelTarget k (labelObs k s) = if s.2 then 1 else -1 := target_path k s

theorem sign_injective (b c : Bool) :
    ((if b then 1 else -1) : ℤ) = (if c then 1 else -1) ↔ b=c := by
  cases b <;> cases c <;> norm_num

theorem label_observations_equal (k : ℕ) (s t : Leaf k × Bool) (e : Edge k) :
    labelObs k s e = labelObs k t e ↔ path k s e = path k t e := by
  simp only [labelObs,labels_coordinate]
  by_cases h : edgeOdd k e = true
  · simp [h]
  · simp [h]

theorem fixed_labels_iff (k : ℕ) (S : Set (Edge k)) :
    Certifies S (labelObs k) (fun s => s.2) ↔ Certifies S (path k) (fun s => s.2) := by
  constructor
  · intro h s t he
    apply h s t
    intro e hm
    exact (label_observations_equal k s t e).mpr (he e hm)
  · intro h s t he
    apply h s t
    intro e hm
    exact (label_observations_equal k s t e).mp (he e hm)

def flipPolicy {I : Type*} (mask : I → Bool) : ReviewPolicy I → ReviewPolicy I
  | .stop b => .stop b
  | .ask i p0 p1 => if mask i then .ask i (flipPolicy mask p1) (flipPolicy mask p0)
      else .ask i (flipPolicy mask p0) (flipPolicy mask p1)

theorem flip_depth {I : Type*} (mask : I → Bool) (p : ReviewPolicy I) :
    policyDepth (flipPolicy mask p) = policyDepth p := by
  induction p with
  | stop b => rfl
  | ask i p0 p1 ih0 ih1 =>
    cases h : mask i <;> simp [flipPolicy,policyDepth,h,ih0,ih1,Nat.max_comm]

theorem flip_run {I X : Type*} (mask : I → Bool) (obs : X → I → Bool)
    (p : ReviewPolicy I) (x : X) :
    policyRun obs (flipPolicy mask p) x =
      policyRun (fun x i => if mask i then !(obs x i) else obs x i) p x := by
  induction p with
  | stop b => rfl
  | ask i p0 p1 ih0 ih1 =>
    cases hm : mask i <;> cases ho : obs x i <;>
      simp [flipPolicy,policyRun,hm,ho,ih0,ih1]

def labelAdaptive (k : ℕ) := flipPolicy (edgeOdd k) (adaptive k)

theorem flow_run_as_labels (k : ℕ) (p : ReviewPolicy (Edge k)) (s : Leaf k × Bool) :
    policyRun (path k) (flipPolicy (edgeOdd k) p) s = policyRun (labelObs k) p s := by
  rw [flip_run]
  apply run_ext
  intro e
  simp [labelObs,labels_coordinate]

theorem labels_run_as_flow (k : ℕ) (p : ReviewPolicy (Edge k)) (s : Leaf k × Bool) :
    policyRun (labelObs k) (flipPolicy (edgeOdd k) p) s = policyRun (path k) p s := by
  rw [flip_run]
  apply run_ext
  intro e
  simp only [labelObs,labels_coordinate]
  by_cases h : edgeOdd k e = true <;> simp [h]

theorem label_adaptive_correct (k : ℕ) (s : Leaf k × Bool) :
    policyRun (labelObs k) (labelAdaptive k) s = s.2 := by
  rw [labelAdaptive,labels_run_as_flow]
  exact adaptive_correct k s

theorem label_adaptive_depth (k : ℕ) : policyDepth (labelAdaptive k) = k+1 := by
  rw [labelAdaptive,flip_depth,adaptive_depth]

theorem label_adaptive_lower (k : ℕ) (p : ReviewPolicy (Edge k))
    (h : ∀ s, policyRun (labelObs k) p s = s.2) : k+1 ≤ policyDepth p := by
  have hl := adaptive_lower k (flipPolicy (edgeOdd k) p) (by intro s; rw [flow_run_as_labels]; exact h s)
  simpa only [flip_depth] using hl

/-- The number of queries actually made on the given feasible input. -/
def runQueries {I X : Type*} (obs : X → I → Bool) : ReviewPolicy I → X → ℕ
  | .stop _, _ => 0
  | .ask i p0 p1, x => 1 + if obs x i then runQueries obs p1 x else runQueries obs p0 x

theorem runQueries_le_depth {I X : Type*} (obs : X → I → Bool)
    (p : ReviewPolicy I) (x : X) : runQueries obs p x ≤ policyDepth p := by
  induction p with
  | stop b => exact le_refl 0
  | ask i p0 p1 ih0 ih1 =>
    simp only [runQueries,policyDepth]
    split <;> omega

/-- Cut off after n queries, preserving any stopping leaf already reached. -/
def cutPolicy {I : Type*} : ℕ → ReviewPolicy I → ReviewPolicy I
  | _, .stop b => .stop b
  | 0, .ask _ _ _ => .stop false
  | n+1, .ask i p0 p1 => .ask i (cutPolicy n p0) (cutPolicy n p1)

theorem cut_depth {I : Type*} (n : ℕ) (p : ReviewPolicy I) :
    policyDepth (cutPolicy n p) ≤ n := by
  induction n generalizing p with
  | zero => cases p <;> exact le_refl 0
  | succ n ih =>
    cases p with
    | stop b => simp [cutPolicy,policyDepth]
    | ask i p0 p1 =>
      simp only [cutPolicy,policyDepth]
      have h0 := ih p0
      have h1 := ih p1
      omega

theorem cut_correct {I X : Type*} (obs : X → I → Bool)
    (n : ℕ) (p : ReviewPolicy I) (x : X) (h : runQueries obs p x ≤ n) :
    policyRun obs (cutPolicy n p) x = policyRun obs p x := by
  induction n generalizing p with
  | zero =>
    cases p with
    | stop b => rfl
    | ask i p0 p1 => simp only [runQueries] at h; split at h <;> omega
  | succ n ih =>
    cases p with
    | stop b => rfl
    | ask i p0 p1 =>
      cases he : obs x i
      · simp only [runQueries,he,Bool.false_eq_true,↓reduceIte] at h
        simpa only [cutPolicy,policyRun,he,Bool.false_eq_true,↓reduceIte] using ih p0 (by omega)
      · simp only [runQueries,he,↓reduceIte] at h
        simpa only [cutPolicy,policyRun,he,↓reduceIte] using ih p1 (by omega)

/-- An actual feasible input forces the lower bound. Unreachable branches
    and redundant queries cannot inflate this witness. -/
theorem label_adaptive_input_lower (k : ℕ) (p : ReviewPolicy (Edge k))
    (h : ∀ s, policyRun (labelObs k) p s = s.2) :
    ∃ s, k+1 ≤ runQueries (labelObs k) p s := by
  classical
  by_contra hn
  have hb : ∀ s, runQueries (labelObs k) p s ≤ k := by
    intro s
    have hn' : ¬ k+1 ≤ runQueries (labelObs k) p s := fun hh => hn ⟨s,hh⟩
    omega
  have hc : ∀ s, policyRun (labelObs k) (cutPolicy k p) s = s.2 := by
    intro s
    rw [cut_correct (labelObs k) k p s (hb s),h s]
  have hl := label_adaptive_lower k (cutPolicy k p) hc
  have hu := cut_depth k p
  omega

theorem label_adaptive_input_upper (k : ℕ) (s : Leaf k × Bool) :
    runQueries (labelObs k) (labelAdaptive k) s ≤ k+1 := by
  exact (runQueries_le_depth _ _ _).trans (le_of_eq (label_adaptive_depth k))

/-- Equality of the actual numeric target on the entire count-feasible set
    is exactly the Boolean certification condition used by the policies. -/
theorem numeric_certification_iff (k : ℕ) (S : Set (Edge k)) :
    (∀ y z, PositiveCounts k y → PositiveCounts k z →
      (∀ e ∈ S, y e = z e) → labelTarget k y = labelTarget k z) ↔
      Certifies S (labelObs k) (fun s => s.2) := by
  constructor
  · intro h s t he
    apply (sign_injective s.2 t.2).mp
    rw [← label_target_sign k s,← label_target_sign k t]
    apply h _ _ ((positive_counts_iff_path k _).mpr ⟨s,rfl⟩)
      ((positive_counts_iff_path k _).mpr ⟨t,rfl⟩) he
  · intro h y z hy hz he
    obtain ⟨s,rfl⟩ := (positive_counts_iff_path k y).mp hy
    obtain ⟨t,rfl⟩ := (positive_counts_iff_path k z).mp hz
    change labelTarget k (labelObs k s) = labelTarget k (labelObs k t)
    rw [label_target_sign,label_target_sign]
    exact (sign_injective s.2 t.2).mpr (h s t he)

def totalCount (k : ℕ) : ℤ := ∑ v, countA k v

theorem groups_sum {E G : Type*} [Fintype E] [Fintype G] [DecidableEq G]
    (g : E → G) (w : E → ℤ) : (∑ v, ∑ e, if g e = v then w e else 0) = ∑ e, w e := by
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  simp

theorem positive_total (k : ℕ) (y : Edge k → Bool) (h : PositiveCounts k y) :
    (∑ e, bit (y e)) = totalCount k := by
  rw [← groups_sum (groupA k) (fun e => bit (y e))]
  change (∑ v, groupCount k (groupA k) y v) = totalCount k
  simp_rw [h.1]
  rfl

def zeroLeaf : (k : ℕ) → Leaf k
  | 0 => ()
  | k+1 => (false,zeroLeaf k)

theorem label_feasible (k : ℕ) (s : Leaf k × Bool) : PositiveCounts k (labelObs k s) :=
  (positive_counts_iff_path k _).mpr ⟨s,rfl⟩

theorem total_nontrivial (k : ℕ) (hk : 1 ≤ k) :
    0 < totalCount k ∧ totalCount k < (Fintype.card (Edge k) : ℤ) := by
  cases k with
  | zero => omega
  | succ k =>
    let y := labelObs (k+1) (zeroLeaf (k+1),true)
    have ht : (∑ e, bit (y e)) = totalCount (k+1) := positive_total _ _ (label_feasible _ _)
    have hn (e : Edge (k+1)) : 0 ≤ bit (y e) := by cases h : y e <;> simp [bit,h]
    have hu (e : Edge (k+1)) : bit (y e) ≤ 1 := by cases h : y e <;> simp [bit,h]
    have hpos : bit (y (.inl false)) = 1 := by simp [y,labelObs,labels,path,zeroLeaf,bit]
    have hzero : bit (y (.inl true)) = 0 := by simp [y,labelObs,labels,path,zeroLeaf,bit]
    constructor
    · have hs := single_le_sum (fun e (_ : e ∈ (univ : Finset (Edge (k+1)))) => hn e)
        (mem_univ (Sum.inl false : Edge (k+1)))
      rw [hpos,ht] at hs
      omega
    · have hs : (∑ e, bit (y e)) < ∑ _ : Edge (k+1), (1:ℤ) := by
        apply sum_lt_sum (fun e _ => hu e)
        exact ⟨.inl true,mem_univ _,by rw [hzero]; norm_num⟩
      simpa [ht] using hs

/-- The paper's full family: positive counts, actual ranks, nondegenerate
    total, and the two matching exact-certification budgets, at every depth. -/
theorem two_partition_separation (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card (Edge k) = 4*2^k-2 ∧
    Function.Bijective (rankFin k false) ∧ Function.Bijective (rankFin k true) ∧
    (∀ y, PositiveCounts k y ↔ ∃ s, y = labelObs k s) ∧
    (∀ s, labelTarget k (labelObs k s) = if s.2 then 1 else -1) ∧
    (0 < totalCount k ∧ totalCount k < (Fintype.card (Edge k) : ℤ)) ∧
    (∀ y, PositiveCounts k y → (∑ e, bit (y e)) = totalCount k) ∧
    ((fixed k).card = 2^k ∧ Certifies (↑(fixed k)) (labelObs k) (fun s => s.2)) ∧
    (∀ S : Finset (Edge k), Certifies (↑S) (labelObs k) (fun s => s.2) → 2^k ≤ S.card) ∧
    (policyDepth (labelAdaptive k) = k+1 ∧ ∀ s, policyRun (labelObs k) (labelAdaptive k) s = s.2) ∧
    (∀ p : ReviewPolicy (Edge k), (∀ s, policyRun (labelObs k) p s = s.2) → k+1 ≤ policyDepth p) ∧
    (∀ s, runQueries (labelObs k) (labelAdaptive k) s ≤ k+1) ∧
    (∀ p : ReviewPolicy (Edge k), (∀ s, policyRun (labelObs k) p s = s.2) →
      ∃ s, k+1 ≤ runQueries (labelObs k) p s) := by
  refine ⟨edge_card k,rank_bijective k false,rank_bijective k true,?_,label_target_sign k,
    total_nontrivial k hk,positive_total k,?_,?_,?_,label_adaptive_lower k,
    label_adaptive_input_upper k,label_adaptive_input_lower k⟩
  · exact positive_counts_iff_path k
  · exact ⟨fixed_card k,(fixed_labels_iff k _).mpr (fixed_correct k)⟩
  · intro S h; exact fixed_lower k S ((fixed_labels_iff k _).mp h)
  · exact ⟨label_adaptive_depth k,label_adaptive_correct k⟩

/-- Correctness on the actual feasible labels, using decoded numeric answers. -/
def NumericPolicyCorrect (k : ℕ) (p : ReviewPolicy (Edge k)) : Prop :=
  ∀ y, PositiveCounts k y →
    ((if policyRun (fun y e => y e) p y then 1 else -1) : ℤ) = labelTarget k y

theorem numeric_policy_iff (k : ℕ) (p : ReviewPolicy (Edge k)) :
    NumericPolicyCorrect k p ↔ ∀ s, policyRun (labelObs k) p s = s.2 := by
  have hr (s : Leaf k × Bool) :
      policyRun (fun y e => y e) p (labelObs k s) = policyRun (labelObs k) p s :=
    run_ext p _ _ _ _ (fun _ => rfl)
  constructor
  · intro h s
    have he := h (labelObs k s) (label_feasible k s)
    rw [label_target_sign,hr] at he
    exact (sign_injective _ _).mp he
  · intro h y hy
    obtain ⟨s,rfl⟩ := (positive_counts_iff_path k y).mp hy
    change ((if policyRun (fun y e => y e) p (labelObs k s) then 1 else -1) : ℤ) =
      labelTarget k (labelObs k s)
    rw [label_target_sign,hr,h s]

theorem runQueries_ext {I X Y : Type*} (p : ReviewPolicy I)
    (o : X → I → Bool) (v : Y → I → Bool) (x : X) (y : Y)
    (h : ∀ i, o x i = v y i) : runQueries o p x = runQueries v p y := by
  induction p with
  | stop b => rfl
  | ask i p0 p1 ih0 ih1 => simp [runQueries,h,ih0,ih1]

/-- Exact numerical certification budgets, quantified directly over all
    positive-count completions and actual input execution costs. -/
theorem exact_numeric_budgets (k : ℕ) :
    ((fixed k).card = 2^k ∧
      ∀ y z, PositiveCounts k y → PositiveCounts k z →
        (∀ e ∈ fixed k, y e = z e) → labelTarget k y = labelTarget k z) ∧
    (∀ S : Finset (Edge k),
      (∀ y z, PositiveCounts k y → PositiveCounts k z →
        (∀ e ∈ S, y e = z e) → labelTarget k y = labelTarget k z) → 2^k ≤ S.card) ∧
    (NumericPolicyCorrect k (labelAdaptive k) ∧
      ∀ y, PositiveCounts k y → runQueries (fun y e => y e) (labelAdaptive k) y ≤ k+1) ∧
    (∀ p, NumericPolicyCorrect k p →
      ∃ y, PositiveCounts k y ∧ k+1 ≤ runQueries (fun y e => y e) p y) := by
  refine ⟨⟨fixed_card k,?_⟩,?_,⟨(numeric_policy_iff k _).mpr (label_adaptive_correct k),?_⟩,?_⟩
  · exact (numeric_certification_iff k _).mpr ((fixed_labels_iff k _).mpr (fixed_correct k))
  · intro S h
    exact fixed_lower k S ((fixed_labels_iff k _).mp ((numeric_certification_iff k _).mp h))
  · intro y hy
    obtain ⟨s,rfl⟩ := (positive_counts_iff_path k y).mp hy
    have he := runQueries_ext (labelAdaptive k) (fun y e => y e) (labelObs k)
      (labelObs k s) s (fun _ => rfl)
    change runQueries (fun y e => y e) (labelAdaptive k) (labelObs k s) ≤ k+1
    rw [he]
    exact label_adaptive_input_upper k s
  · intro p hp
    obtain ⟨s,hs⟩ := label_adaptive_input_lower k p ((numeric_policy_iff k p).mp hp)
    refine ⟨labelObs k s,label_feasible k s,?_⟩
    have he := runQueries_ext p (fun y e => y e) (labelObs k)
      (labelObs k s) s (fun _ => rfl)
    rw [he]
    exact hs

def aucDenominator (k : ℕ) : ℝ :=
  (totalCount k : ℝ) * ((Fintype.card (Edge k) : ℝ) - (totalCount k : ℝ))

theorem auc_denominator_positive (k : ℕ) (hk : 1 ≤ k) : 0 < aucDenominator k := by
  obtain ⟨hp,hu⟩ := total_nontrivial k hk
  apply positive_denominator
  · exact_mod_cast hp
  · exact_mod_cast hu

theorem normalized_exactness (k : ℕ) (hk : 1 ≤ k) (y z : Edge k → Bool) :
    (labelTarget k y : ℝ) / aucDenominator k = (labelTarget k z : ℝ) / aucDenominator k ↔
      labelTarget k y = labelTarget k z := by
  rw [div_left_inj' (ne_of_gt (auc_denominator_positive k hk))]
  exact Int.cast_inj

end FusionTree
