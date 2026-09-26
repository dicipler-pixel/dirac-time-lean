/- FALSE CONTROL: Corollary P4.2 needs a non-scalar reference generator.
   With H₀ = I, the generators 1·I + 0·I and 0·I + 1·I are equal, yet the rates 1 and 0
   differ. Claiming equality of the generators forces equal rates must fail.
   This file must not compile. -/
import Mathlib

theorem scalar_generator_fixes_rate :
    ((1:ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) + (0:ℚ) • 1 = (0:ℚ) • 1 + (1:ℚ) • 1) →
      (1:ℚ) = 0 := by
  simp
