import EvidenceFusion

open scoped BigOperators
open Finset

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvidenceFusion
noncomputable section

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype Ω] [DecidableEq Ω]

theorem upperRank_permutation (s : ι → ℝ) (σ : Equiv.Perm ι) (i : ι) :
    upperRank (fun j => s (σ j)) i = upperRank s (σ i) := by
  unfold upperRank
  apply Finset.card_bij (fun j _ => σ j)
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  · intro j _ k _ hjk
    exact σ.injective hjk
  · intro j hj
    refine ⟨σ.symm j, ?_, σ.apply_symm_apply j⟩
    simpa using hj

def rankProbability (p : Ω → ℝ) (X : Ω → ι → ℝ) (q : ℕ) (i : ι) : ℝ :=
  ∑ ω, p ω * (if upperRank (X ω) i ≤ q then 1 else 0)

/-- A finite probability law invariant under every permutation of reports.
This is an explicit finite-law version of exchangeability, not an assumption
that the desired rank probability bound already holds. -/
def FiniteExchangeable (p : Ω → ℝ) (X : Ω → ι → ℝ) : Prop :=
  ∀ σ : Equiv.Perm ι, ∃ τ : Equiv.Perm Ω,
    (∀ ω, p (τ ω) = p ω) ∧ (∀ ω i, X (τ ω) i = X ω (σ i))

theorem rank_probability_equal (p : Ω → ℝ) (X : Ω → ι → ℝ)
    (hex : FiniteExchangeable p X) (q : ℕ) (i j : ι) :
    rankProbability p X q i = rankProbability p X q j := by
  obtain ⟨τ, hp, hX⟩ := hex (Equiv.swap i j)
  have hR : ∀ ω, upperRank (X (τ ω)) i = upperRank (X ω) j := by
    intro ω
    have he : X (τ ω) = fun k => X ω (Equiv.swap i j k) := by
      funext k; exact hX ω k
    rw [he, upperRank_permutation]
    simp
  unfold rankProbability
  calc
    ∑ ω, p ω * (if upperRank (X ω) i ≤ q then 1 else 0) =
        ∑ ω, p (τ ω) * (if upperRank (X (τ ω)) i ≤ q then 1 else 0) :=
      (Equiv.sum_comp τ _).symm
    _ = _ := by apply Finset.sum_congr rfl; intro ω _; rw [hp, hR]

/-- Conservative rank validity for every finite exchangeable probability law. -/
theorem finite_exchangeable_rank_bound (p : Ω → ℝ) (X : Ω → ι → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (hex : FiniteExchangeable p X) (q : ℕ) (i : ι) :
    rankProbability p X q i ≤ (q : ℝ)/Fintype.card ι := by
  have hcount : ∀ ω, (∑ j : ι, (if upperRank (X ω) j ≤ q then (1:ℝ) else 0)) ≤ q := by
    intro ω
    have h := rank_count_le (X ω) q
    have hc : (∑ j : ι, (if upperRank (X ω) j ≤ q then (1:ℝ) else 0)) =
        ((Finset.univ.filter fun j => upperRank (X ω) j ≤ q).card : ℝ) := by simp
    rw [hc]
    exact_mod_cast h
  have hsum : ∑ j, rankProbability p X q j ≤ q := by
    unfold rankProbability
    rw [Finset.sum_comm]
    calc
      ∑ ω, ∑ j, p ω * (if upperRank (X ω) j ≤ q then 1 else 0) ≤
          ∑ ω, p ω * (q:ℝ) := by
        apply Finset.sum_le_sum
        intro ω _
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hcount ω) (hp ω)
      _ = q := by rw [← Finset.sum_mul, hp1, one_mul]
  have heq : (∑ j, rankProbability p X q j) =
      (Fintype.card ι : ℝ)*rankProbability p X q i := by
    calc
      _ = ∑ _j : ι, rankProbability p X q i := by
        apply Finset.sum_congr rfl
        intro j _
        exact rank_probability_equal p X hex q j i
      _ = _ := by simp
  rw [heq] at hsum
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  exact (le_div_iff₀ hn).mpr (by nlinarith)

/-- The rank-evidence mixture in S11 for finite exchangeable laws. -/
theorem finite_rank_evidence {L : Type*} [Fintype L]
    (p : Ω → ℝ) (X : Ω → ι → ℝ) (v : L → ℝ) (q : L → ℕ) (i : ι)
    (hp : ∀ ω, 0 ≤ p ω) (hp1 : ∑ ω, p ω = 1)
    (hex : FiniteExchangeable p X)
    (hv : ∀ l, 0 ≤ v l) (hv1 : ∑ l, v l = 1) (hq : ∀ l, 0 < q l) :
    ∑ ω, p ω * (∑ l, v l * ((Fintype.card ι : ℝ)/q l) *
      (if upperRank (X ω) i ≤ q l then 1 else 0)) ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ l, ((Fintype.card ι : ℝ)/q l)*rankProbability p X (q l) i ≤ 1 := by
    intro l
    have hql : (0 : ℝ) < q l := by exact_mod_cast hq l
    have h := mul_le_mul_of_nonneg_left
      (finite_exchangeable_rank_bound p X hp hp1 hex (q l) i)
      (div_nonneg hn.le hql.le)
    have hc : ((Fintype.card ι : ℝ)/q l)*((q l:ℝ)/Fintype.card ι) = 1 := by
      field_simp
    simpa [hc] using h
  calc
    _ = ∑ l, v l * (((Fintype.card ι : ℝ)/q l)*rankProbability p X (q l) i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      unfold rankProbability
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ ∑ l, v l*1 := by
      exact Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hterm l) (hv l)
    _ = 1 := by simpa using hv1

end
end EvidenceFusion
