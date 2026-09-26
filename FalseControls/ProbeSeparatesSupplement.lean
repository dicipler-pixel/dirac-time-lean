/- FALSE CONTROL: the sin-probe cannot tell a Wilson phase Φ from π − Φ.
   Claiming it separates Φ = 1 from π − 1 must fail. This file must not compile. -/
import Mathlib

theorem probe_separates : Real.sin (Real.pi - 1) ≠ Real.sin 1 := by
  simp
