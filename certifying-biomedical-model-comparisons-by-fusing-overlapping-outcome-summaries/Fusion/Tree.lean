import Fusion.Review
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum

namespace FusionTree
open Finset

/-- Leaves of a complete binary tree of depth k. -/
def Leaf : ℕ → Type
  | 0 => Unit
  | k+1 => Bool × Leaf k

def Edge : ℕ → Type
  | 0 => Bool
  | k+1 => Bool ⊕ (Bool × Edge k)

instance leafDecEq (k : ℕ) : DecidableEq (Leaf k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ k ih => exact inferInstanceAs (DecidableEq (Bool × Leaf k))
instance edgeDecEq (k : ℕ) : DecidableEq (Edge k) := by
  induction k with
  | zero => exact inferInstanceAs (DecidableEq Bool)
  | succ k ih => exact inferInstanceAs (DecidableEq (Bool ⊕ (Bool × Edge k)))
instance leafFintype (k : ℕ) : Fintype (Leaf k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih => exact inferInstanceAs (Fintype (Bool × Leaf k))
instance edgeFintype (k : ℕ) : Fintype (Edge k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype Bool)
  | succ k ih => exact inferInstanceAs (Fintype (Bool ⊕ (Bool × Edge k)))

def bit (b : Bool) : ℤ := if b then 1 else 0

def path : (k : ℕ) → Leaf k × Bool → Edge k → Bool
  | 0, x, b => decide (x.2 = b)
  | k+1, x, .inl b => decide (x.1.1 = b)
  | k+1, x, .inr (b,e) => decide (x.1.1 = b) && path k (x.1.2,x.2) e

/-- Unit-capacity conservation at the root and recursively in both subtrees.
    At depth zero the two arcs are the parallel payload arcs to the sink. -/
def Flow : (k : ℕ) → (Edge k → Bool) → Bool → Prop
  | 0, x, u => bit (x false) + bit (x true) = bit u
  | k+1, x, u =>
      bit (x (.inl false)) + bit (x (.inl true)) = bit u ∧
      ∀ b, Flow k (fun e => x (.inr (b,e))) (x (.inl b))

theorem leaf_card (k : ℕ) : Fintype.card (Leaf k) = 2^k := by
  induction k with
  | zero => simp [Leaf]
  | succ k ih => simp only [Leaf, Fintype.card_prod, Fintype.card_bool, ih]; ring

theorem edge_card (k : ℕ) : Fintype.card (Edge k) = 4*2^k-2 := by
  induction k with
  | zero => simp [Edge]
  | succ k ih =>
    simp only [Edge,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,ih]
    have h : 0 < (2:ℕ)^k := by positivity
    rw [pow_succ]
    omega

theorem zero_flow (k : ℕ) : Flow k (fun _ => false) false := by
  induction k with
  | zero => rfl
  | succ k ih => exact ⟨rfl,fun _ => ih⟩

theorem zero_unique (k : ℕ) (x : Edge k → Bool) (h : Flow k x false) :
    ∀ e, x e = false := by
  induction k with
  | zero =>
    have hh := h
    simp only [Flow] at hh
    cases h0 : x false <;> cases h1 : x true <;> simp [bit,h0,h1] at hh
    intro e; cases e <;> assumption
  | succ k ih =>
    obtain ⟨hroot,hsub⟩ := h
    have h0 : x (.inl false) = false := by
      cases h0 : x (.inl false) <;> cases h1 : x (.inl true) <;> simp_all [bit]
    have h1 : x (.inl true) = false := by
      cases h1 : x (.inl true) <;> simp_all [bit]
    intro e
    cases e with
    | inl b => cases b <;> assumption
    | inr be =>
      apply ih (fun e => x (.inr (be.1,e)))
      have hb : x (.inl be.1) = false := by cases be.1 <;> assumption
      simpa [hb] using hsub be.1

theorem path_feasible (k : ℕ) (s : Leaf k × Bool) : Flow k (path k s) true := by
  induction k with
  | zero => cases hs : s.2 <;> simp [Flow,path,bit,hs]
  | succ k ih =>
    constructor
    · cases hs : s.1.1 <;> simp [path,bit,hs]
    · intro b
      by_cases hb : s.1.1 = b
      · simpa [path,hb] using ih (s.1.2,s.2)
      · simpa [path,hb] using zero_flow k

/-- For every depth, every feasible unit binary flow is an advertised path state. -/
theorem path_exhaustive (k : ℕ) (x : Edge k → Bool) (h : Flow k x true) :
    ∃ s : Leaf k × Bool, x = path k s := by
  induction k with
  | zero =>
    change bit (x false) + bit (x true) = 1 at h
    cases h0 : x false <;> cases h1 : x true <;> simp [bit,h0,h1] at h
    · refine ⟨((),true),?_⟩; funext b; cases b <;> simp [path,h0,h1]
    · refine ⟨((),false),?_⟩; funext b; cases b <;> simp [path,h0,h1]
  | succ k ih =>
    obtain ⟨hr,hs⟩ := h
    have hex : ∃ b : Bool, x (.inl b) = true ∧ x (.inl (!b)) = false := by
      cases h0 : x (.inl false) <;> cases h1 : x (.inl true) <;> simp [bit,h0,h1] at hr
      · exact ⟨true,h1,h0⟩
      · exact ⟨false,h0,h1⟩
    obtain ⟨b,hb,hnb⟩ := hex
    obtain ⟨s,he⟩ := ih (fun e => x (.inr (b,e))) (by simpa [hb] using hs b)
    have hz := zero_unique k (fun e => x (.inr (!b,e))) (by simpa [hnb] using hs (!b))
    refine ⟨((b,s.1),s.2),?_⟩
    funext e
    cases e with
    | inl c => cases b <;> cases c <;> simp_all [path]
    | inr ce =>
      obtain ⟨c,e⟩ := ce
      have ha := congrFun he e
      have hn := hz e
      cases b <;> cases c <;> simp_all [path]

/-- Distinct addresses or signs produce different record vectors at every depth. -/
theorem path_injective (k : ℕ) : Function.Injective (path k) := by
  induction k with
  | zero =>
    intro s t he
    have h := congrFun he s.2
    have hb : s.2 = t.2 := by simpa [path,eq_comm] using h
    have ha : s.1 = t.1 := by
      change (s.1 : Unit) = (t.1 : Unit)
      exact @Subsingleton.elim Unit inferInstance s.1 t.1
    exact Prod.ext ha hb
  | succ k ih =>
    intro s t he
    have h := congrFun he (.inl s.1.1)
    have hb : s.1.1 = t.1.1 := by simpa [path,eq_comm] using h
    have hsub : path k (s.1.2,s.2) = path k (t.1.2,t.2) := by
      funext e
      have h := congrFun he (.inr (s.1.1,e))
      simpa [path,hb] using h
    have hc := ih hsub
    have ht : s.1.2 = t.1.2 := congrArg (fun z : Leaf k × Bool => z.1) hc
    have hs : s.2 = t.2 := congrArg (fun z : Leaf k × Bool => z.2) hc
    exact Prod.ext (Prod.ext hb ht) hs

open Fusion

def mapPolicy {I J : Type*} (f : I → J) : ReviewPolicy I → ReviewPolicy J
  | .stop b => .stop b
  | .ask i p0 p1 => .ask (f i) (mapPolicy f p0) (mapPolicy f p1)

theorem map_depth {I J : Type*} (f : I → J) (p : ReviewPolicy I) :
    policyDepth (mapPolicy f p) = policyDepth p := by
  induction p with
  | stop b => rfl
  | ask i p0 p1 ih0 ih1 => simp [mapPolicy,policyDepth,ih0,ih1]

theorem map_run {I J X : Type*} (f : I → J) (obs : X → J → Bool)
    (p : ReviewPolicy I) (x : X) :
    policyRun obs (mapPolicy f p) x = policyRun (fun x i => obs x (f i)) p x := by
  induction p with
  | stop b => rfl
  | ask i p0 p1 ih0 ih1 => simp [mapPolicy,policyRun,ih0,ih1]

theorem run_ext {I X Y : Type*} (p : ReviewPolicy I) (o : X → I → Bool)
    (v : Y → I → Bool) (x : X) (y : Y) (h : ∀ i, o x i = v y i) :
    policyRun o p x = policyRun v p y := by
  induction p with
  | stop b => rfl
  | ask i p0 p1 ih0 ih1 => simp [policyRun,h,ih0,ih1]

/-- Query one outgoing arc at each reached node, then the plus payload. -/
def adaptive : (k : ℕ) → ReviewPolicy (Edge k)
  | 0 => .ask true (.stop false) (.stop true)
  | k+1 => .ask (.inl true)
      (mapPolicy (fun e => Sum.inr (false,e)) (adaptive k))
      (mapPolicy (fun e => Sum.inr (true,e)) (adaptive k))

theorem adaptive_depth (k : ℕ) : policyDepth (adaptive k) = k+1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [adaptive,policyDepth,map_depth,ih]; omega

theorem adaptive_correct (k : ℕ) (s : Leaf k × Bool) :
    policyRun (path k) (adaptive k) s = s.2 := by
  induction k with
  | zero => cases hs : s.2 <;> simp [adaptive,policyRun,path,hs]
  | succ k ih =>
    cases hb : s.1.1
    · simp only [adaptive,policyRun,path,hb,Bool.false_eq_true,decide_false,if_false,map_run]
      rw [run_ext (adaptive k) _ (path k) s (s.1.2,s.2) (by intro e; simp [path,hb])]
      exact ih (s.1.2,s.2)
    · simp only [adaptive,policyRun,path,hb,decide_true,if_true,map_run]
      rw [run_ext (adaptive k) _ (path k) s (s.1.2,s.2) (by intro e; simp [path,hb])]
      exact ih (s.1.2,s.2)

def payload : (k : ℕ) → Leaf k × Bool → Edge k
  | 0, s => s.2
  | k+1, s => .inr (s.1.1,payload k (s.1.2,s.2))

theorem payload_injective (k : ℕ) : Function.Injective (payload k) := by
  induction k with
  | zero =>
    intro s t h
    have ha : s.1 = t.1 := by
      change (s.1 : Unit) = (t.1 : Unit)
      exact @Subsingleton.elim Unit inferInstance s.1 t.1
    exact Prod.ext ha h
  | succ k ih =>
    intro s t h
    have he : (s.1.1,payload k (s.1.2,s.2)) = (t.1.1,payload k (t.1.2,t.2)) := Sum.inr.inj h
    have hc := ih (congrArg Prod.snd he)
    have hb : s.1.1 = t.1.1 := congrArg (fun z : Bool × Edge k => z.1) he
    have ht : s.1.2 = t.1.2 := congrArg (fun z : Leaf k × Bool => z.1) hc
    have hs : s.2 = t.2 := congrArg (fun z : Leaf k × Bool => z.2) hc
    exact Prod.ext (Prod.ext hb ht) hs

theorem path_payload (k : ℕ) (s t : Leaf k × Bool) :
    path k s (payload k t) = decide (s = t) := by
  induction k with
  | zero =>
    have ha : s.1 = t.1 := by
      change (s.1 : Unit) = (t.1 : Unit)
      exact @Subsingleton.elim Unit inferInstance s.1 t.1
    simp [path,payload,Prod.ext_iff,ha]
  | succ k ih =>
    obtain ⟨⟨a,x⟩,b⟩ := s
    obtain ⟨⟨c,y⟩,d⟩ := t
    have he : (((a,x),b) : Leaf (k+1) × Bool) = ((c,y),d) ↔ (a=c ∧ x=y) ∧ b=d := by
      change (((a,x),b) : (Bool × Leaf k) × Bool) = ((c,y),d) ↔ _
      simp only [Prod.mk.injEq]
    simp only [path,payload,ih,he,Prod.mk.injEq,Bool.decide_and,Bool.and_assoc]

def fixed (k : ℕ) : Finset (Edge k) :=
  univ.image (fun a : Leaf k => payload k (a,true))

theorem fixed_card (k : ℕ) : (fixed k).card = 2^k := by
  rw [fixed,card_image_of_injective]
  · exact leaf_card k
  · intro a b h; exact congrArg Prod.fst (payload_injective k h)

theorem fixed_correct (k : ℕ) : Certifies (↑(fixed k)) (path k) (fun s => s.2) := by
  intro s t h
  have hmem (a : Leaf k) : payload k (a,true) ∈ fixed k := mem_image.mpr ⟨a,mem_univ _,rfl⟩
  have h1 := h (payload k (s.1,true)) (hmem s.1)
  have h2 := h (payload k (t.1,true)) (hmem t.1)
  simp only [path_payload,Prod.mk.injEq,true_and] at h1 h2
  cases hs : s.2 <;> cases ht : t.2 <;> simp_all [Prod.ext_iff]

def kind : (k : ℕ) → Edge k → Option (Leaf k × Bool)
  | 0, e => some ((),e)
  | k+1, .inl _ => none
  | k+1, .inr (b,e) => (kind k e).map (fun s => ((b,s.1),s.2))

theorem kind_some (k : ℕ) (e : Edge k) (s : Leaf k × Bool)
    (h : kind k e = some s) : e = payload k s := by
  induction k with
  | zero => simpa [kind,payload] using congrArg (Option.map Prod.snd) h
  | succ k ih =>
    cases e with
    | inl b => simp [kind] at h
    | inr be =>
      obtain ⟨b,e⟩ := be
      cases he : kind k e with
      | none => simp [kind,he] at h
      | some t =>
        have hs : ((b,t.1),t.2) = s := by simpa [kind,he] using h
        subst s
        simp only [payload]
        rw [ih e t he]

theorem kind_none (k : ℕ) (e : Edge k) (h : kind k e = none)
    (a : Leaf k) (b c : Bool) : path k (a,b) e = path k (a,c) e := by
  induction k with
  | zero => simp [kind] at h
  | succ k ih =>
    cases e with
    | inl d => rfl
    | inr de =>
      obtain ⟨d,e⟩ := de
      have he : kind k e = none := by
        cases hh : kind k e <;> simp_all [kind]
      simp only [path]
      rw [ih e he a.2]

noncomputable def leafFin (k : ℕ) := Fintype.equivFin (Leaf k)
noncomputable def encodedQuery (k : ℕ) (e : Edge k) :
    PairQuery (Fintype.card (Leaf k)) (Edge k) :=
  match kind k e with
  | none => .inl e
  | some s => .inr (leafFin k s.1,s.2)
noncomputable def addressObservation (k : ℕ)
    (a : Fin (Fintype.card (Leaf k))) (e : Edge k) : Bool :=
  path k ((leafFin k).symm a,false) e

theorem path_encoded (k : ℕ) (s : Leaf k × Bool) (e : Edge k) :
    path k s e = pairObs (addressObservation k) (leafFin k s.1,s.2) (encodedQuery k e) := by
  cases h : kind k e with
  | none =>
    simp only [encodedQuery,h,pairObs,addressObservation,Equiv.symm_apply_apply]
    exact kind_none k e h s.1 s.2 false
  | some t =>
    have he := kind_some k e t h
    simp only [encodedQuery,h,pairObs]
    rw [he,path_payload]
    simp [Prod.ext_iff,Equiv.apply_eq_iff_eq,Bool.decide_and]

theorem fixed_lower (k : ℕ) (S : Finset (Edge k))
    (h : Certifies (↑S) (path k) (fun s => s.2)) : 2^k ≤ S.card := by
  classical
  let T := S.image (encodedQuery k)
  have hc : Certifies (↑T) (pairObs (addressObservation k)) (fun s => s.2) := by
    intro s t he
    apply h ((leafFin k).symm s.1,s.2) ((leafFin k).symm t.1,t.2)
    intro e hm
    have hh := he (encodedQuery k e) (mem_image.mpr ⟨e,hm,rfl⟩)
    simpa only [path_encoded,Equiv.apply_symm_apply] using hh
  have hl := fixed_budget_lower (addressObservation k) T hc
  have hu : T.card ≤ S.card := card_image_le
  calc
    2^k = Fintype.card (Leaf k) := (leaf_card k).symm
    _ ≤ T.card := hl
    _ ≤ S.card := hu

theorem adaptive_lower (k : ℕ) (p : ReviewPolicy (Edge k))
    (h : ∀ s, policyRun (path k) p s = s.2) : k+1 ≤ policyDepth p := by
  classical
  by_contra hn
  have hd : policyDepth (mapPolicy (encodedQuery k) p) ≤ k := by rw [map_depth]; omega
  apply adaptive_pair_lower (addressObservation k) k
    (mapPolicy (encodedQuery k) p) univ hd
  · simp [leaf_card]
  · intro a ha b
    rw [map_run]
    rw [run_ext p _ (path k) (a,b) ((leafFin k).symm a,b) (by
      intro e
      simpa only [Equiv.apply_symm_apply] using
        (path_encoded k ((leafFin k).symm a,b) e).symm)]
    exact h _

/-- Both exact worst-case budgets, now on the explicit tree-flow states. -/
theorem review_optima (k : ℕ) :
    ((fixed k).card = 2^k ∧ Certifies (↑(fixed k)) (path k) (fun s => s.2)) ∧
    (∀ S : Finset (Edge k), Certifies (↑S) (path k) (fun s => s.2) → 2^k ≤ S.card) ∧
    (policyDepth (adaptive k) = k+1 ∧ ∀ s, policyRun (path k) (adaptive k) s = s.2) ∧
    (∀ p : ReviewPolicy (Edge k), (∀ s, policyRun (path k) p s = s.2) → k+1 ≤ policyDepth p) :=
  ⟨⟨fixed_card k,fixed_correct k⟩,fixed_lower k,
    ⟨adaptive_depth k,adaptive_correct k⟩,adaptive_lower k⟩

end FusionTree
