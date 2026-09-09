import ParitySources

open OverlapReconstruction Set
open scoped BigOperators

namespace RepeatedEvidenceProbability

def PatternSource (n : ℕ) (f : Cube n → ℤ) : Type :=
  Σ x : Cube n, Fin ((f x).toNat)

instance patternSourceFintype (n : ℕ) (f : Cube n → ℤ) : Fintype (PatternSource n f) :=
  inferInstanceAs (Fintype (Σ x : Cube n, Fin ((f x).toNat)))

noncomputable def patternOverlap (n : ℕ) (f : Cube n → ℤ) (R : Cube n) : ℕ :=
  ∑ v : PatternSource n f, if cubeExtends n R v.1 then 1 else 0

theorem patternSource_weight_sum (n : ℕ) (f w : Cube n → ℤ) (hf : ∀ x, 0 ≤ f x) :
    (∑ v : PatternSource n f, w v.1) = ∑ x : Cube n, f x * w x := by
  change (∑ v : (Σ x : Cube n, Fin ((f x).toNat)), w v.1) = _
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro x _
  simp [Int.toNat_of_nonneg (hf x)]

theorem patternOverlap_eq_zeta (n : ℕ) (f : Cube n → ℤ) (hf : ∀ x, 0 ≤ f x) (R : Cube n) :
    (patternOverlap n f R : ℤ) = zeta n f R := by
  unfold patternOverlap
  rw [zeta_eq_pattern_sum]
  push_cast
  calc
    _ = ∑ x : Cube n, f x * (if cubeExtends n R x then (1:ℤ) else 0) :=
      patternSource_weight_sum n f (fun x => if cubeExtends n R x then 1 else 0) hf
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp

theorem patternOverlap_empty_card (n : ℕ) (f : Cube n → ℤ) :
    patternOverlap n f (empty n) = Fintype.card (PatternSource n f) := by
  simp [patternOverlap,cubeExtends_empty]

/-- Actual proper intersection counts, including the total-source query,
determine every exact-pattern multiplicity when unused sources are absent. -/
theorem proper_source_overlaps_reconstruct (n : ℕ) (f g : Cube n → ℤ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hf0 : f (empty n) = 0) (hg0 : g (empty n) = 0)
    (hproper : ∀ R, R ≠ full n → patternOverlap n f R = patternOverlap n g R) : f = g := by
  apply proper_intersections_reconstruct n f g hf0 hg0
  intro R hR
  rw [← patternOverlap_eq_zeta n f hf R,← patternOverlap_eq_zeta n g hg R,hproper R hR]

/-- The reconstructed canonical source sets agree up to a bijection that
preserves every source's entire sharing pattern. -/
theorem proper_source_overlaps_relabel (n : ℕ) (f g : Cube n → ℤ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hf0 : f (empty n) = 0) (hg0 : g (empty n) = 0)
    (hproper : ∀ R, R ≠ full n → patternOverlap n f R = patternOverlap n g R) :
    ∃ e : PatternSource n f ≃ PatternSource n g, ∀ v, (e v).1 = v.1 := by
  have h := proper_source_overlaps_reconstruct n f g hf hg hf0 hg0 hproper
  subst g
  exact ⟨Equiv.refl _,fun _ => rfl⟩

end RepeatedEvidenceProbability
