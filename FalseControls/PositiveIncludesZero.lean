-- FALSE CONTROL: DT-C008 replaces t > 0 by the claim that a visible present state is hidden.
import Mathlib
theorem zero_generator_is_hidden : ∀ t : ℝ, 0 < t → (1 : ℝ) = 0 := by
  intro t ht
  linarith
