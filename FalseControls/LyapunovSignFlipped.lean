-- FALSE CONTROL: DT-C297 with γ = -1, the dissipation -γ v² is positive.
import Mathlib
theorem lyapunov_wrong_sign : -(-1 : ℚ) * (1 : ℚ) ^ 2 ≤ 0 := by
  norm_num
