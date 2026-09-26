/- FALSE CONTROL: a loop with nonzero ledger admits no endpoint potential.
   One point, one loop of ledger 1: a potential would need 1 = n(x) - n(x) = 0.
   This file must not compile. -/
import Mathlib

theorem loop_has_potential : ∃ n : Unit → ℤ, (1 : ℤ) = n () - n () :=
  ⟨fun _ => 0, by simp⟩
