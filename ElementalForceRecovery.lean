import Mathlib

/-!
# Elemental nonlinear-force recovery certificates

Finite algebraic certificates for the cubic-coupling example in the elemental
foundations manuscript. The model statement is conditional on the declared
polynomial force law and calibrated coordinates. It is not an atom-removal
law or a material fit.
-/

namespace ElementalFoundations

noncomputable section

/-- The z-force at z=0 for the declared cubic interaction coefficients.
The exact decimal coefficients in the manuscript are represented rationally:
0.05=1/20, 0.03=3/100, 0.04=1/25. -/
def zForce (sα sβ sγ x y : ℝ) : ℝ :=
  -((1/20 : ℝ) * sα * x * y +
    (3/100 : ℝ) * sβ * x^2 +
    (1/25 : ℝ) * sγ * y^2)

@[simp] theorem zForce_origin (sα sβ sγ : ℝ) :
    zForce sα sβ sγ 0 0 = 0 := by
  simp [zForce]

theorem zForce_x_axis (sα sβ sγ a : ℝ) :
    zForce sα sβ sγ a 0 = -(3/100 : ℝ) * sβ * a^2 := by
  unfold zForce
  ring

theorem zForce_y_axis (sα sβ sγ a : ℝ) :
    zForce sα sβ sγ 0 a = -(1/25 : ℝ) * sγ * a^2 := by
  unfold zForce
  ring

theorem zForce_diagonal (sα sβ sγ a : ℝ) :
    zForce sα sβ sγ a a =
      -(1/20 : ℝ) * sα * a^2 -
      (3/100 : ℝ) * sβ * a^2 -
      (1/25 : ℝ) * sγ * a^2 := by
  unfold zForce
  ring

theorem recover_sbeta (sα sβ sγ a : ℝ) (ha : a ≠ 0) :
    sβ = - zForce sα sβ sγ a 0 / ((3/100 : ℝ) * a^2) := by
  rw [zForce_x_axis]
  field_simp [ha]

theorem recover_sgamma (sα sβ sγ a : ℝ) (ha : a ≠ 0) :
    sγ = - zForce sα sβ sγ 0 a / ((1/25 : ℝ) * a^2) := by
  rw [zForce_y_axis]
  field_simp [ha]

theorem recover_salpha (sα sβ sγ a : ℝ) (ha : a ≠ 0) :
    sα = -(
      zForce sα sβ sγ a a -
      zForce sα sβ sγ a 0 -
      zForce sα sβ sγ 0 a) / ((1/20 : ℝ) * a^2) := by
  rw [zForce_diagonal, zForce_x_axis, zForce_y_axis]
  field_simp [ha]
  ring

/-- Three calibrated z-force readings recover all three attenuation
parameters exactly in the declared polynomial model. -/
theorem three_force_recovery (sα sβ sγ a : ℝ) (ha : a ≠ 0) :
    sβ = - zForce sα sβ sγ a 0 / ((3/100 : ℝ) * a^2) ∧
    sγ = - zForce sα sβ sγ 0 a / ((1/25 : ℝ) * a^2) ∧
    sα = -(
      zForce sα sβ sγ a a -
      zForce sα sβ sγ a 0 -
      zForce sα sβ sγ 0 a) / ((1/20 : ℝ) * a^2) := by
  exact ⟨recover_sbeta sα sβ sγ a ha,
    recover_sgamma sα sβ sγ a ha,
    recover_salpha sα sβ sγ a ha⟩

/-- A measured force with a common additive calibration offset. -/
def observedZForce (offset sα sβ sγ x y : ℝ) : ℝ :=
  offset + zForce sα sβ sγ x y

theorem observed_x_difference (offset sα sβ sγ a : ℝ) :
    observedZForce offset sα sβ sγ a 0 -
      observedZForce offset sα sβ sγ 0 0 =
      zForce sα sβ sγ a 0 := by
  simp [observedZForce]

theorem observed_y_difference (offset sα sβ sγ a : ℝ) :
    observedZForce offset sα sβ sγ 0 a -
      observedZForce offset sα sβ sγ 0 0 =
      zForce sα sβ sγ 0 a := by
  simp [observedZForce]

theorem observed_diagonal_combination (offset sα sβ sγ a : ℝ) :
    observedZForce offset sα sβ sγ a a -
      observedZForce offset sα sβ sγ a 0 -
      observedZForce offset sα sβ sγ 0 a +
      observedZForce offset sα sβ sγ 0 0 =
      zForce sα sβ sγ a a -
      zForce sα sβ sγ a 0 -
      zForce sα sβ sγ 0 a := by
  unfold observedZForce
  rw [zForce_origin]
  ring

/-- Four readings remove an unknown common force offset and recover all three
cubic attenuation parameters exactly. -/
theorem four_force_recovery_with_offset
    (offset sα sβ sγ a : ℝ) (ha : a ≠ 0) :
    sβ = -(
      observedZForce offset sα sβ sγ a 0 -
      observedZForce offset sα sβ sγ 0 0) / ((3/100 : ℝ) * a^2) ∧
    sγ = -(
      observedZForce offset sα sβ sγ 0 a -
      observedZForce offset sα sβ sγ 0 0) / ((1/25 : ℝ) * a^2) ∧
    sα = -(
      observedZForce offset sα sβ sγ a a -
      observedZForce offset sα sβ sγ a 0 -
      observedZForce offset sα sβ sγ 0 a +
      observedZForce offset sα sβ sγ 0 0) / ((1/20 : ℝ) * a^2) := by
  rw [observed_x_difference, observed_y_difference,
    observed_diagonal_combination]
  exact ⟨recover_sbeta sα sβ sγ a ha,
    recover_sgamma sα sβ sγ a ha,
    recover_salpha sα sβ sγ a ha⟩

/-- Deterministic error propagation for the three-readout recovery formulas.
If each force reading has absolute error at most δ, then the alpha numerator
inherits at most 3δ. -/
theorem three_reading_error_combination {e10 e01 e11 δ : ℝ}
    (h10 : |e10| ≤ δ) (h01 : |e01| ≤ δ) (h11 : |e11| ≤ δ) :
    |e11 - e10 - e01| ≤ 3*δ := by
  rcases abs_le.mp h10 with ⟨h10L, h10U⟩
  rcases abs_le.mp h01 with ⟨h01L, h01U⟩
  rcases abs_le.mp h11 with ⟨h11L, h11U⟩
  apply abs_le.mpr
  constructor <;> linarith

/-- With an additional offset reading, the inclusion-exclusion numerator for
alpha inherits at most four times the per-reading absolute error. -/
theorem four_reading_error_combination {e00 e10 e01 e11 δ : ℝ}
    (h00 : |e00| ≤ δ) (h10 : |e10| ≤ δ)
    (h01 : |e01| ≤ δ) (h11 : |e11| ≤ δ) :
    |e11 - e10 - e01 + e00| ≤ 4*δ := by
  rcases abs_le.mp h00 with ⟨h00L, h00U⟩
  rcases abs_le.mp h10 with ⟨h10L, h10U⟩
  rcases abs_le.mp h01 with ⟨h01L, h01U⟩
  rcases abs_le.mp h11 with ⟨h11L, h11U⟩
  apply abs_le.mpr
  constructor <;> linarith

end

end ElementalFoundations

#print axioms ElementalFoundations.zForce_origin
#print axioms ElementalFoundations.zForce_x_axis
#print axioms ElementalFoundations.zForce_y_axis
#print axioms ElementalFoundations.zForce_diagonal
#print axioms ElementalFoundations.recover_sbeta
#print axioms ElementalFoundations.recover_sgamma
#print axioms ElementalFoundations.recover_salpha
#print axioms ElementalFoundations.three_force_recovery
#print axioms ElementalFoundations.observed_x_difference
#print axioms ElementalFoundations.observed_y_difference
#print axioms ElementalFoundations.observed_diagonal_combination
#print axioms ElementalFoundations.four_force_recovery_with_offset
#print axioms ElementalFoundations.three_reading_error_combination
#print axioms ElementalFoundations.four_reading_error_combination
