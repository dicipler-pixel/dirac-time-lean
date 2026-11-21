-- FALSE CONTROL: DT-C192 the factor in front of the square root is 1, not 2.
import Mathlib
theorem curvature_factor : |2 * (1 : ℝ)| ≤ 1 * Real.sqrt (1 * 1 - 0) := by
  norm_num
