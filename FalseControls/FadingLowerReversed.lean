-- FALSE CONTROL: DT-C305 lower bound e^{-νu} A ≤ A_ν fails if the weight is dropped below 0.
import Mathlib
theorem fading_weight_nonpositive : Real.exp (-1) * 2 ≤ 0 := by
  have := Real.exp_pos (-1)
  linarith
