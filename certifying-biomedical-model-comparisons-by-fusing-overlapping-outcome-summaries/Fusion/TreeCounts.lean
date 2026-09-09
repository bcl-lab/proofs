import Fusion.TreeRank

namespace FusionTree
open Finset

@[reducible] def Node : ℕ → Type
  | 0 => Unit
  | k+1 => Option (Bool × Node k)

instance nodeDecEq (k : ℕ) : DecidableEq (Node k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ k ih => exact inferInstanceAs (DecidableEq (Option (Bool × Node k)))
instance nodeFintype (k : ℕ) : Fintype (Node k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih => exact inferInstanceAs (Fintype (Option (Bool × Node k)))

def root : (k : ℕ) → Node k
  | 0 => ()
  | _+1 => none

def origin : (k : ℕ) → Edge k → Node k
  | 0, _ => ()
  | _+1, .inl _ => none
  | k+1, .inr (b,e) => some (b,origin k e)

/-- The outer none denotes the common sink. -/
def destination : (k : ℕ) → Edge k → Option (Node k)
  | 0, _ => none
  | k+1, .inl b => some (some (b,root k))
  | k+1, .inr (b,e) => (destination k e).map (fun v => some (b,v))

def nodeOdd : (k : ℕ) → Node k → Bool
  | 0, _ => false
  | _+1, none => false
  | k+1, some (_,v) => !(nodeOdd k v)
def sinkOdd : ℕ → Bool
  | 0 => true
  | k+1 => !(sinkOdd k)
def edgeOdd : (k : ℕ) → Edge k → Bool
  | 0, _ => false
  | _+1, .inl _ => false
  | k+1, .inr (_,e) => !(edgeOdd k e)
def side (k : ℕ) (v : Option (Node k)) : Bool :=
  v.elim (sinkOdd k) (nodeOdd k)

theorem root_even (k : ℕ) : nodeOdd k (root k) = false := by cases k <;> rfl

theorem origin_parity (k : ℕ) (e : Edge k) : nodeOdd k (origin k e) = edgeOdd k e := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases e with
    | inl b => rfl
    | inr be => simp [origin,nodeOdd,edgeOdd,ih]

theorem destination_parity (k : ℕ) (e : Edge k) :
    side k (destination k e) = !(edgeOdd k e) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases e with
    | inl b => simp [side,destination,nodeOdd,edgeOdd,root_even]
    | inr be =>
      obtain ⟨b,e⟩ := be
      have h := ih e
      cases hd : destination k e <;> simp_all [side,destination,nodeOdd,edgeOdd,sinkOdd]

def groupA (k : ℕ) (e : Edge k) : Option (Node k) :=
  if edgeOdd k e then destination k e else some (origin k e)
def groupB (k : ℕ) (e : Edge k) : Option (Node k) :=
  if edgeOdd k e then some (origin k e) else destination k e

/-- Every record is assigned once to each of the two vertex partitions. -/
theorem group_sides (k : ℕ) (e : Edge k) :
    side k (groupA k e) = false ∧ side k (groupB k e) = true := by
  have ho := origin_parity k e
  have hd := destination_parity k e
  cases he : edgeOdd k e <;> simp_all [groupA,groupB,side]

theorem labels_coordinate (k : ℕ) (x : Edge k → Bool) (e : Edge k) :
    labels k x e = if edgeOdd k e then !(x e) else x e := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases e with
    | inl b => rfl
    | inr be =>
      obtain ⟨b,e⟩ := be
      simp only [labels,edgeOdd,ih]
      by_cases he : edgeOdd k e = true
      · simp [he]
      · have hf : edgeOdd k e = false := Bool.eq_false_iff.mpr he
        simp [hf]

def outgoing (k : ℕ) (x : Edge k → Bool) (v : Node k) : ℤ :=
  ∑ e, if origin k e = v then bit (x e) else 0
def incoming (k : ℕ) (x : Edge k → Bool) (v : Node k) : ℤ :=
  ∑ e, if destination k e = some v then bit (x e) else 0
def nodeBalance (k : ℕ) (x : Edge k → Bool) (v : Node k) : ℤ :=
  outgoing k x v - incoming k x v

theorem outgoing_root (k : ℕ) (x : Edge (k+1) → Bool) :
    outgoing (k+1) x (root (k+1)) = bit (x (.inl false)) + bit (x (.inl true)) := by
  simp [outgoing,Edge,root,origin,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,add_comm]

theorem node_pair_eq (k : ℕ) (b c : Bool) (u v : Node k) :
    (some (b,u) : Node (k+1)) = some (c,v) ↔ b=c ∧ u=v := by
  change (some (b,u) : Option (Bool × Node k)) = some (c,v) ↔ _
  simp only [Option.some.injEq,Prod.mk.injEq]

theorem node_some_ne_root (k : ℕ) (b : Bool) (v : Node k) :
    (some (b,v) : Node (k+1)) ≠ root (k+1) := by
  change (some (b,v) : Option (Bool × Node k)) ≠ none
  simp

theorem outgoing_child (k : ℕ) (x : Edge (k+1) → Bool) (b : Bool) (v : Node k) :
    outgoing (k+1) x (some (b,v)) = outgoing k (fun e => x (.inr (b,e))) v := by
  cases b <;> simp [outgoing,Edge,origin,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,node_pair_eq k]

theorem incoming_root (k : ℕ) (x : Edge (k+1) → Bool) :
    incoming (k+1) x (root (k+1)) = 0 := by
  apply sum_eq_zero
  intro e he
  cases e with
  | inl b => simp [destination,root]
  | inr be =>
    obtain ⟨b,e⟩ := be
    cases hd : destination k e <;> simp [destination,root,hd]

theorem incoming_child (k : ℕ) (x : Edge (k+1) → Bool) (b : Bool) (v : Node k) :
    incoming (k+1) x (some (b,v)) =
      incoming k (fun e => x (.inr (b,e))) v +
        (if v = root k then bit (x (.inl b)) else 0) := by
  have childEq (c d : Bool) (e : Edge k) :
      destination (k+1) (.inr (c,e)) = some (some (d,v)) ↔ c=d ∧ destination k e = some v := by
    cases hd : destination k e <;> simp [destination,hd,node_pair_eq k]
  have rootEq (c d : Bool) :
      destination (k+1) (.inl c) = some (some (d,v)) ↔ c=d ∧ root k = v := by
    simp [destination,node_pair_eq k]
  have root_comm : root k = v ↔ v = root k := eq_comm
  cases b <;>
    simp only [incoming,Edge,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
      childEq,rootEq,root_comm]
  all_goals simp only [Bool.true_eq_false,Bool.false_eq_true,not_false_eq_true,and_true,
    and_false,true_and,false_and,ite_true,ite_false,sum_const_zero,zero_add,add_zero]
  all_goals rw [add_comm]

/-- The recursive path equations are the actual network conservation equations. -/
theorem flow_conservation (k : ℕ) (x : Edge k → Bool) (u : Bool) :
    Flow k x u ↔ ∀ v, nodeBalance k x v = if v = root k then bit u else 0 := by
  induction k generalizing u with
  | zero =>
    constructor
    · intro h v
      have hv : v = root 0 := @Subsingleton.elim Unit inferInstance v (root 0)
      simpa [nodeBalance,outgoing,incoming,Edge,origin,destination,Flow,Fintype.sum_bool,hv,root,add_comm] using h
    · intro h
      simpa [nodeBalance,outgoing,incoming,Edge,origin,destination,Flow,Fintype.sum_bool,root,add_comm] using h (root 0)
  | succ k ih =>
    constructor
    · rintro ⟨hr,hs⟩ v
      cases v with
      | none =>
        change nodeBalance (k+1) x (root (k+1)) = bit u
        rw [nodeBalance,outgoing_root,incoming_root,sub_zero]
        exact hr
      | some bv =>
        obtain ⟨b,v⟩ := bv
        have h := (ih (fun e => x (.inr (b,e))) (x (.inl b))).mp (hs b) v
        rw [nodeBalance,outgoing_child,incoming_child]
        change _ = 0
        dsimp [nodeBalance] at h
        omega
    · intro h
      refine ⟨?_,?_⟩
      · have hr := h (root (k+1))
        rw [nodeBalance,outgoing_root,incoming_root] at hr
        simpa using hr
      · intro b
        apply (ih (fun e => x (.inr (b,e))) (x (.inl b))).mpr
        intro v
        have hc : nodeBalance (k+1) x (some (b,v)) = 0 := by
          simpa only [if_neg (node_some_ne_root k b v)] using h (some (b,v))
        simp only [nodeBalance,outgoing_child,incoming_child] at hc
        dsimp [nodeBalance]
        omega

def fullBalance (k : ℕ) (x : Edge k → Bool) (v : Option (Node k)) : ℤ :=
  (∑ e, if some (origin k e) = v then bit (x e) else 0) -
    ∑ e, if destination k e = v then bit (x e) else 0

def supply (k : ℕ) (u : Bool) (v : Option (Node k)) : ℤ :=
  if v = some (root k) then bit u else if v = none then -bit u else 0

theorem fullBalance_node (k : ℕ) (x : Edge k → Bool) (v : Node k) :
    fullBalance k x (some v) = nodeBalance k x v := by
  simp [fullBalance,nodeBalance,outgoing,incoming]

theorem balance_sum (k : ℕ) (x : Edge k → Bool) : (∑ v, fullBalance k x v) = 0 := by
  simp only [fullBalance,sum_sub_distrib]
  have regroup (f : Edge k → Option (Node k)) :
      (∑ v, ∑ e, if f e = v then bit (x e) else 0) = ∑ e, bit (x e) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro e he
    simp
  rw [regroup,regroup,sub_self]

theorem full_conservation (k : ℕ) (x : Edge k → Bool) (u : Bool) :
    Flow k x u ↔ ∀ v, fullBalance k x v = supply k u v := by
  constructor
  · intro hf
    have hn := (flow_conservation k x u).mp hf
    have hs : (∑ v : Node k, fullBalance k x (some v)) = bit u := by
      simp_rw [fullBalance_node,hn]
      simp
    have hb := balance_sum k x
    rw [Fintype.sum_option,hs] at hb
    intro v
    cases v with
    | none => simp [supply]; omega
    | some v => simpa [fullBalance_node,supply] using hn v
  · intro h
    apply (flow_conservation k x u).mpr
    intro v
    simpa [fullBalance_node,supply] using h (some v)

def groupCount {G : Type*} [DecidableEq G] (k : ℕ) (g : Edge k → G)
    (y : Edge k → Bool) (v : G) : ℤ := ∑ e, if g e = v then bit (y e) else 0
def offset {G : Type*} [DecidableEq G] (k : ℕ) (g : Edge k → G) (v : G) : ℤ :=
  ∑ e, if g e = v ∧ edgeOdd k e = true then 1 else 0
def signedGroup {G : Type*} [DecidableEq G] (k : ℕ) (g : Edge k → G)
    (x : Edge k → Bool) (v : G) : ℤ :=
  ∑ e, if g e = v then (if edgeOdd k e then -bit (x e) else bit (x e)) else 0

theorem complemented_count {G : Type*} [DecidableEq G]
    (k : ℕ) (g : Edge k → G) (x : Edge k → Bool) (v : G) :
    groupCount k g (labels k x) v = signedGroup k g x v + offset k g v := by
  rw [groupCount,signedGroup,offset,← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  by_cases hg : g e = v <;> cases ho : edgeOdd k e <;>
    simp [hg,ho,labels_coordinate,bit_not] <;> omega

theorem balance_groups (k : ℕ) (x : Edge k → Bool) (v : Option (Node k)) :
    fullBalance k x v = signedGroup k (groupA k) x v - signedGroup k (groupB k) x v := by
  simp only [fullBalance,signedGroup,← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  cases ho : edgeOdd k e <;> simp [groupA,groupB,ho] <;> split_ifs <;> ring

theorem inactive_groupA (k : ℕ) (x : Edge k → Bool) (v : Option (Node k))
    (hv : side k v = true) : signedGroup k (groupA k) x v = 0 := by
  apply sum_eq_zero
  intro e he
  have hne : groupA k e ≠ v := by
    intro h
    have hs := (group_sides k e).1
    rw [h,hv] at hs
    cases hs
  simp [hne]

theorem inactive_groupB (k : ℕ) (x : Edge k → Bool) (v : Option (Node k))
    (hv : side k v = false) : signedGroup k (groupB k) x v = 0 := by
  apply sum_eq_zero
  intro e he
  have hne : groupB k e ≠ v := by
    intro h
    have hs := (group_sides k e).2
    rw [h,hv] at hs
    cases hs
  simp [hne]

def countA (k : ℕ) (v : Option (Node k)) : ℤ :=
  (if side k v then 0 else supply k true v) + offset k (groupA k) v
def countB (k : ℕ) (v : Option (Node k)) : ℤ :=
  (if side k v then -supply k true v else 0) + offset k (groupB k) v

/-- Ordinary exact positive counts from two actual partitions of the records. -/
def PositiveCounts (k : ℕ) (y : Edge k → Bool) : Prop :=
  (∀ v, groupCount k (groupA k) y v = countA k v) ∧
  (∀ v, groupCount k (groupB k) y v = countB k v)

theorem flow_positive_counts (k : ℕ) (x : Edge k → Bool) :
    PositiveCounts k (labels k x) ↔ Flow k x true := by
  rw [full_conservation]
  constructor
  · rintro ⟨ha,hb⟩ v
    have hA := ha v
    have hB := hb v
    rw [complemented_count,countA] at hA
    rw [complemented_count,countB] at hB
    rw [balance_groups]
    cases hs : side k v <;> simp only [hs,if_true,if_false,Bool.false_eq_true] at hA hB <;> omega
  · intro h
    constructor <;> intro v
    · rw [complemented_count,countA]
      have hv := h v
      rw [balance_groups] at hv
      cases hs : side k v
      · rw [inactive_groupB k x v hs,sub_zero] at hv
        simp [hs,hv]
      · simp [hs,inactive_groupA k x v hs]
    · rw [complemented_count,countB]
      have hv := h v
      rw [balance_groups] at hv
      cases hs : side k v
      · simp [hs,inactive_groupB k x v hs]
      · rw [inactive_groupA k x v hs] at hv
        simp [hs]
        omega

/-- Completeness and soundness of the all-depth two-partition realization. -/
theorem positive_counts_iff_path (k : ℕ) (y : Edge k → Bool) :
    PositiveCounts k y ↔ ∃ s : Leaf k × Bool, y = labels k (path k s) := by
  constructor
  · intro h
    have hf : Flow k (labels k y) true := by
      apply (flow_positive_counts k (labels k y)).mp
      simpa [labels_involution] using h
    obtain ⟨s,hs⟩ := path_exhaustive k (labels k y) hf
    refine ⟨s,?_⟩
    have he := congrArg (labels k) hs
    simpa [labels_involution] using he
  · rintro ⟨s,rfl⟩
    exact (flow_positive_counts k (path k s)).mpr (path_feasible k s)

end FusionTree
