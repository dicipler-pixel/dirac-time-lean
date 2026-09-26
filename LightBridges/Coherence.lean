import Mathlib

/-! Curvature and compression keep their noncommutative ordering.
NOT COMPILED in this environment. No homotopy-transfer theorem is claimed. -/
set_option autoImplicit false

namespace LightBridges
section CovariantSquare
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- Three-edge covariant square, valid before any flatness assumption. -/
theorem covariant_square (a b c : R) (s0 s1 s2 : V) :
    a • (b • s2 - s1) - (c • s2 - s0) + (a • s1 - s0) =
      (a * b - c) • s2 := by
  simp only [smul_sub, sub_smul, mul_smul]
  abel

end CovariantSquare

section GroupCoherence
variable {G : Type*} [Group G]

/-- Holonomy on an ordered triangle; c transports directly along its long edge. -/
def face (a b c : G) : G := a * b * c⁻¹

/-- Exact nonabelian tetrahedral compatibility.
a=U01, b=U12, c=U02, d=U23, e=U03, f=U13. -/
theorem tetrahedral (a b c d e f : G) :
    face a b c * face c d e = a * face b d f * a⁻¹ * face a f e := by
  unfold face
  group

/-- Flatness is the composition law, not an independent scalar cancellation. -/
theorem face_flat_iff (a b c : G) : face a b c = 1 ↔ a * b = c := by
  unfold face
  exact mul_inv_eq_one

end GroupCoherence

section Compression
variable {R : Type*} [Ring R]

/-- An additive compression's discarded terms account for its associator.
Idempotence is only needed to interpret the result as a product on the image. -/
theorem compression_associator (P : R →+ R) (x y z : R) :
    P (P (x * y) * z) - P (x * P (y * z)) =
      P (x * (y * z - P (y * z)) - (x * y - P (x * y)) * z) := by
  have h : x * (y * z - P (y * z)) - (x * y - P (x * y)) * z =
      P (x * y) * z - x * P (y * z) := by noncomm_ring
  rw [h, map_sub]

/-- If both intermediate products survive compression, this associator vanishes. -/
theorem compression_associator_zero (P : R →+ R) (x y z : R)
    (hxy : P (x * y) = x * y) (hyz : P (y * z) = y * z) :
    P (P (x * y) * z) - P (x * P (y * z)) = 0 := by
  rw [compression_associator, hxy, hyz]
  simp

end Compression
end LightBridges
