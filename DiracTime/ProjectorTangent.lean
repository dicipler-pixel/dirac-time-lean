/-
Star-projection tangent geometry (Theorem P1 and programme item T2 of "The Dirac Time of
the Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978631).

Proved here:
* Tangent characterization. For an idempotent `P` with complement `Q = 1 - P`, a velocity
  `V` satisfies the differentiated projector equation `P V + V P = V` exactly when both
  diagonal blocks vanish, `P V P = 0` and `Q V Q = 0`; such a `V` is purely off-diagonal,
  `V = P V Q + Q V P`. (Any ring.)
* Metric positivity. `g(V, V) = ½ Tr(V V)` is strictly positive on nonzero self-adjoint
  complex matrices.
* Unitary covariance. Conjugating the projector and both tangents by a unitary leaves
  `Tr(V W)` and `Tr(P [V, W])` unchanged, so `g_P` and `Ω_P` are unitarily invariant.

Not proved here: the block formulas `g = Re Tr(X Y†)`, `Ω = -2 Im Tr(X Y†)` and the
metric-curvature inequality (items 2 and 3 of Theorem P1).
-/
import Mathlib

namespace DiracTime.ProjectorTangent

/-! ## Tangent characterization (any ring) -/

section Ring

variable {R : Type*} [Ring R]

/-- Differentiating `P(t)² = P(t)` gives `P V + V P = V`; that forces the occupied
diagonal block to vanish. -/
theorem occupied_block_zero {P V : R} (hP : P * P = P) (hV : P * V + V * P = V) :
    P * V * P = 0 := by
  calc P * V * P = P * (P * V + V * P) - P * P * V := by noncomm_ring
    _ = P * V - P * V := by rw [hV, hP]
    _ = 0 := sub_self _

/-- The complementary diagonal block vanishes too. -/
theorem complement_block_zero {P V : R} (hP : P * P = P) (hV : P * V + V * P = V) :
    (1 - P) * V * (1 - P) = 0 := by
  calc (1 - P) * V * (1 - P) = V - (P * V + V * P) + P * V * P := by noncomm_ring
    _ = 0 := by rw [hV, occupied_block_zero hP hV, sub_self, add_zero]

/-- Conversely, vanishing of both diagonal blocks gives the tangent equation. -/
theorem tangent_of_blocks_zero {P V : R} (h1 : P * V * P = 0)
    (h2 : (1 - P) * V * (1 - P) = 0) : P * V + V * P = V := by
  calc P * V + V * P = V - (1 - P) * V * (1 - P) + P * V * P := by noncomm_ring
    _ = V := by rw [h1, h2, sub_zero, add_zero]

/-- Tangent characterization: the tangent equation holds exactly when both diagonal
blocks vanish. -/
theorem tangent_iff_blocks_zero {P V : R} (hP : P * P = P) :
    P * V + V * P = V ↔ P * V * P = 0 ∧ (1 - P) * V * (1 - P) = 0 :=
  ⟨fun hV => ⟨occupied_block_zero hP hV, complement_block_zero hP hV⟩,
    fun h => tangent_of_blocks_zero h.1 h.2⟩

/-- Every tangent is purely off-diagonal: `V = P V Q + Q V P`. -/
theorem tangent_eq_offdiag {P V : R} (hP : P * P = P) (hV : P * V + V * P = V) :
    V = P * V * (1 - P) + (1 - P) * V * P := by
  calc V = P * V * (1 - P) + (1 - P) * V * P + P * V * P + (1 - P) * V * (1 - P) := by
        noncomm_ring
    _ = P * V * (1 - P) + (1 - P) * V * P := by
        rw [occupied_block_zero hP hV, complement_block_zero hP hV, add_zero, add_zero]

end Ring

/-! ## Metric positivity (complex matrices) -/

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

open Matrix
open scoped ComplexOrder

/-- The trace form `Tr(V† V)` is strictly positive on every nonzero matrix. -/
theorem trace_conjTranspose_mul_self_re_pos {V : Matrix n n ℂ} (hV : V ≠ 0) :
    0 < (trace (Vᴴ * V)).re := by
  have hpsd : (Vᴴ * V).PosSemidef := posSemidef_conjTranspose_mul_self V
  have hle : (0 : ℂ) ≤ trace (Vᴴ * V) := hpsd.trace_nonneg
  have hne : trace (Vᴴ * V) ≠ 0 := by
    intro h0
    exact hV (conjTranspose_mul_self_eq_zero.mp ((hpsd.trace_eq_zero_iff).mp h0))
  have hlt : (0 : ℂ) < trace (Vᴴ * V) := lt_of_le_of_ne hle (Ne.symm hne)
  exact (Complex.lt_def.mp hlt).1

/-- Metric positivity: `g(V, V) = ½ Tr(V V)` is strictly positive on every nonzero
self-adjoint tangent. -/
theorem metric_pos {V : Matrix n n ℂ} (hH : Vᴴ = V) (hV : V ≠ 0) :
    0 < (trace (V * V)).re / 2 := by
  have h := trace_conjTranspose_mul_self_re_pos hV
  rw [hH] at h
  linarith

/-! ## Unitary covariance -/

/-- Conjugation by a unitary preserves products. -/
theorem conj_mul {U : Matrix n n ℂ} (hU : star U * U = 1) (A B : Matrix n n ℂ) :
    (U * A * star U) * (U * B * star U) = U * (A * B) * star U := by
  calc (U * A * star U) * (U * B * star U) = U * (A * (star U * U) * B) * star U := by
        simp only [Matrix.mul_assoc]
    _ = U * (A * B) * star U := by rw [hU, Matrix.mul_one]

/-- Conjugation by a unitary preserves the trace. -/
theorem trace_conj {U : Matrix n n ℂ} (hU : star U * U = 1) (X : Matrix n n ℂ) :
    trace (U * X * star U) = trace X := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul]

/-- Unitary covariance of the metric: `Tr(V' W') = Tr(V W)` for `V' = U V U†`,
`W' = U W U†`. -/
theorem metric_unitary_invariant {U : Matrix n n ℂ} (hU : star U * U = 1)
    (V W : Matrix n n ℂ) :
    trace ((U * V * star U) * (U * W * star U)) = trace (V * W) := by
  rw [conj_mul hU, trace_conj hU]

/-- Unitary covariance of the curvature form: `Tr(P' [V', W']) = Tr(P [V, W])`. -/
theorem curvature_unitary_invariant {U : Matrix n n ℂ} (hU : star U * U = 1)
    (P V W : Matrix n n ℂ) :
    trace ((U * P * star U) * ((U * V * star U) * (U * W * star U) -
        (U * W * star U) * (U * V * star U))) =
      trace (P * (V * W - W * V)) := by
  rw [conj_mul hU V W, conj_mul hU W V, ← Matrix.sub_mul, ← Matrix.mul_sub, conj_mul hU,
    trace_conj hU]

end Matrix

end DiracTime.ProjectorTangent
