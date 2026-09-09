import EvidenceFusion

set_option autoImplicit false

-- This file is intentionally expected to fail. Three positive reports do
-- not reach evidence 20 when B = 50 and one replacement is allowed.
theorem false_report_count : (20 : ℝ) ≤ 50*(1-2*1/3) := by
  norm_num
