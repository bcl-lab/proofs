import Std

set_option maxHeartbeats 1000000
namespace RepeatedEvidenceCore

def parityWeight : Nat → Nat → Bool → Nat
  | 0, r, b => if b then 0 else r
  | n+1, r, b => parityWeight n r b + parityWeight n (r+1) (!b)

theorem parityWeight_closed (n r : Nat) (b : Bool) :
    parityWeight (n+2) r b = (2*r+n+2) * 2^n := by
  induction n generalizing r b with
  | zero => cases b <;> simp [parityWeight] <;> omega
  | succ n ih =>
    change parityWeight (n+2) r b + parityWeight (n+2) (r+1) (!b) = _
    rw [ih, ih, Nat.pow_succ, ← Nat.add_mul, Nat.mul_comm (2^n) 2, ← Nat.mul_assoc]
    congr 1
    omega

#print axioms parityWeight_closed
end RepeatedEvidenceCore

namespace RepeatedEvidenceCore

theorem overlap_count_formula (m r : Nat) (h : r+2 ≤ m) (b : Bool) :
    parityWeight (m-r) r b = (m+r) * 2^(m-r-2) := by
  have he : m-r = (m-r-2)+2 := by omega
  rw [he, parityWeight_closed]
  have hc : 2*r+(m-r-2)+2 = m+r := by omega
  rw [hc]
  congr 1

theorem overlap_parities_equal (m r : Nat) (h : r+2 ≤ m) :
    parityWeight (m-r) r false = parityWeight (m-r) r true := by
  rw [overlap_count_formula m r h false, overlap_count_formula m r h true]

theorem parity_union_size (m : Nat) (hm : 2 ≤ m) (b : Bool) :
    parityWeight m 0 b = m * 2^(m-2) := by
  simpa using overlap_count_formula m 0 hm b

/-- Rows of the source-by-study incidence matrices, encoded as bit masks.
Repeated entries are distinct sources with the same sharing pattern. -/
def rowsA : List Nat := [3,3,5,5,6,6,9,9,10,10,12,12,15,15,15,15]
def rowsB : List Nat := [1,2,4,8,7,7,7,11,11,11,13,13,13,14,14,14]
def degree (mask : Nat) : Nat := ([0,1,2,3].filter fun i => mask.testBit i).length
def overlap (rows : List Nat) (mask : Nat) : Nat :=
  (rows.filter fun row => (row &&& mask) == mask).length

theorem four_study_counts : ∀ R : Fin 16, degree R.val ≤ 2 →
    overlap rowsA R.val = overlap rowsB R.val ∧
    overlap rowsA R.val = if degree R.val = 0 then 16 else if degree R.val = 1 then 10 else 6 := by
  decide

theorem four_study_full_counts : overlap rowsA 15 = 4 ∧ overlap rowsB 15 = 0 := by decide

theorem four_study_maximum_reads :
    (∀ v ∈ rowsA, degree v ≤ 4) ∧ (∃ v ∈ rowsA, degree v = 4) ∧
    (∀ v ∈ rowsB, degree v ≤ 3) ∧ (∃ v ∈ rowsB, degree v = 3) := by
  decide

/-- Nine active sources in each B study justify assigning weight one ninth
to each source that is shared by three studies. -/
theorem four_study_nine_active_sources : ∀ i : Fin 4,
    (rowsB.filter fun v => degree v == 3 && v.testBit i.val).length = 9 := by
  decide

#print axioms overlap_count_formula
#print axioms overlap_parities_equal
#print axioms parity_union_size
#print axioms four_study_counts
#print axioms four_study_full_counts
#print axioms four_study_maximum_reads
#print axioms four_study_nine_active_sources
end RepeatedEvidenceCore
