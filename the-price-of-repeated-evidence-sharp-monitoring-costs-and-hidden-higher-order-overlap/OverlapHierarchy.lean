import ParityCalibration

open OverlapReconstruction ParityIncidence MeasureTheory Set
open scoped ENNReal BigOperators

namespace RepeatedEvidenceProbability

/-- Theorem 3 as a single statement about actual source sets, intersection
counts, union sizes and exact universal stochastic monitoring costs. -/
theorem overlap_hierarchy (m : ℕ) (hm : 3 ≤ m) (a : ℝ)
    (ha0 : 1/(m:ℝ) ≤ a) (ha1 : a < 1/((m-1:ℕ):ℝ)) :
    (∀ R : Cube m, degree m R + 2 ≤ m →
      parityOverlap m (fullParity m) R = parityOverlap m (!(fullParity m)) R ∧
      parityOverlap m (fullParity m) R = (m+degree m R)*2^(m-degree m R-2)) ∧
    Fintype.card (ParitySource m (fullParity m)) = m*2^(m-2) ∧
    Fintype.card (ParitySource m (!(fullParity m))) = m*2^(m-2) ∧
    universalCost (parityUses m (fullParity m)) (fun _ => a) = ∞ ∧
    universalCost (parityUses m (!(fullParity m))) (fun _ => a) =
      ENNReal.ofReal ((1-((m-1:ℕ):ℝ)*a)^(-((m:ℝ)/((m-1:ℕ):ℝ)))) := by
  have hm0 : 0 < m := by omega
  have hm2 : 2 ≤ m := by omega
  have hm' : (0:ℝ) < m := by exact_mod_cast hm0
  have ha : 0 < a := (one_div_pos.mpr hm').trans_le ha0
  refine ⟨?_,paritySource_union_card m hm2 _,paritySource_union_card m hm2 _,
    paritySourceA_infinite m hm0 a ha0,paritySourceB_exact_cost m hm2 a ha ha1⟩
  intro R hR
  rw [paritySource_intersections m (fullParity m) R hR,
    paritySource_intersections m (!(fullParity m)) R hR]
  exact ⟨rfl,rfl⟩

/-- Corollary 3.1 for every member of the actual all-orders construction. -/
theorem overlap_hierarchy_capped (m : ℕ) (hm : 3 ≤ m) (H a : ℝ)
    (hH : 1 ≤ H) (ha : 0 < a) :
    universalCappedCost (parityUses m (fullParity m)) H (fun _ => a) =
      ENNReal.ofReal (RepeatedEvidence.capMoment H ((m:ℝ)*a)) ∧
    universalCappedCost (parityUses m (!(fullParity m))) H (fun _ => a) ≤
      ENNReal.ofReal ((RepeatedEvidence.capMoment H (((m-1:ℕ):ℝ)*a))^
        ((m:ℝ)/((m-1:ℕ):ℝ))) := by
  classical
  have hm0 : 0 < m := by omega
  have hm' : (0:ℝ) < m := by exact_mod_cast hm0
  have hd : (0:ℝ) < (m-1:ℕ) := by exact_mod_cast (show 0 < m-1 by omega)
  constructor
  · have h := universalCappedCost_common_source (parityUses m (fullParity m))
      (fun _ => a) (fun _ => ha.le) (paritySourceA_full m hm0)
      (paritySourceA_full_uses m hm0) H hH (by simpa using mul_pos hm' ha)
    simpa using h
  · have h := universalCappedCost_le_read_bound (parityUses m (!(fullParity m)))
      H a ((m-1:ℕ):ℝ) hH ha hd (fun v => ?_)
    · simpa using h
    · rw [paritySource_read_sum]
      exact_mod_cast (show degree m v.1 ≤ m-1 by have := paritySource_B_read_lt m v; omega)

end RepeatedEvidenceProbability
