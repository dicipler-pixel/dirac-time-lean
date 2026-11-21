-- FALSE CONTROL: geometric identity with the wrong endpoint x^N + 1.
import Mathlib
theorem geom_sum_plus :
    ((∑ i ∈ Finset.range 2, (2 : ℚ) ^ i) * (2 - 1)) = 2 ^ 2 + 1 := by
  norm_num
