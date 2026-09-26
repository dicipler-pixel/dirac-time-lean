/- FALSE CONTROL: the frame connection cannot be dropped.
   One dimension, ħ = 1, frame R(t) = e^{it}: at t = 0, R = 1 and Ṙ = i. With H = 0 the true
   state is constant, so χ̇ = −i χ; the spectrum-only generator R† H R = 0 would give χ̇ = 0.
   Claiming i·χ̇ = (R† H R) χ with χ̇ = −i and χ = 1 must fail. This file must not compile. -/
import Mathlib

theorem spectrum_only_generator : Complex.I * (-Complex.I) = (0 : ℂ) * 1 := by
  simp
