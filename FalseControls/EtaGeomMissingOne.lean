-- FALSE CONTROL: DT-C223 factor 1 - (1-η)^N replaced by (1-η)^N.
import Mathlib
theorem eta_geom_flipped :
    (1 / 2 : ℚ) * ∑ n ∈ Finset.range 2, (1 - 1 / 2) ^ n = (1 - 1 / 2) ^ 2 := by
  norm_num
