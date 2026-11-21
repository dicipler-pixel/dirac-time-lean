-- FALSE CONTROL: DT-C067 without idempotence. P = [[0,1],[1,0]] is not a projector
-- and the two sides differ: LHS = 0, RHS = I - P.
import Mathlib
-- Evaluated entries: for P = [[0,1],[1,0]] and H = 1, the left side is 0 and the
-- right side is I - P, whose (0,0) entry is 1.
theorem coupling_without_idempotent : (0 : ℚ) = 1 := by
  norm_num
