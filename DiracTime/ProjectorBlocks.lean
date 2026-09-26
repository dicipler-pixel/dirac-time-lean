/-
Block formulas for the projector metric and curvature (Theorem P1, item 2 of "The Dirac
Time of the Gigantefermion", Jeromie Beasley, DOI 10.5281/zenodo.22978631).

Split the space as `Ran P ⊕ Ran Q`, so that `P = [[1, 0], [0, 0]]` and a tangent at `P` is
`V = [[0, X], [X†, 0]]`. With `g(V, W) = ½ Tr(V W)`, `Ω(V, W) = i Tr(P [V, W])` and
`Q(A, B) = Tr(P A† B)`, proved here:

* the block tangent is self-adjoint and both of its diagonal blocks vanish;
* `g(V, W) = Re Tr(X Y†)`;
* `Ω(V, W) = −2 Im Tr(X Y†)`;
* `Q(V, W) = Tr(X Y†) = g(V, W) − (i/2) Ω(V, W)`.
-/
import Mathlib

namespace DiracTime.ProjectorBlocks

open Matrix Complex

variable {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]

/-- The tangent at `P` with off-diagonal block `X`. -/
def tangentBlock (X : Matrix m p ℂ) : Matrix (m ⊕ p) (m ⊕ p) ℂ := fromBlocks 0 X Xᴴ 0

/-- The projector onto the first summand. -/
def occ : Matrix (m ⊕ p) (m ⊕ p) ℂ := fromBlocks 1 0 0 0

/-- The complementary projector. -/
def vac : Matrix (m ⊕ p) (m ⊕ p) ℂ := fromBlocks 0 0 0 1

theorem occ_add_comp : (occ : Matrix (m ⊕ p) (m ⊕ p) ℂ) + vac = 1 := by
  rw [← fromBlocks_one]
  simp [occ, vac, fromBlocks_add]

theorem occ_idem : (occ : Matrix (m ⊕ p) (m ⊕ p) ℂ) * occ = occ := by
  simp [occ, fromBlocks_multiply]

theorem tangentBlock_conjTranspose (X : Matrix m p ℂ) : (tangentBlock X)ᴴ = tangentBlock X := by
  simp [tangentBlock, fromBlocks_conjTranspose]

/-- Both diagonal blocks of a block tangent vanish. -/
theorem tangentBlock_is_tangent (X : Matrix m p ℂ) :
    occ * tangentBlock X * occ = 0 ∧ vac * tangentBlock X * vac = 0 := by
  constructor <;> simp [occ, vac, tangentBlock, fromBlocks_multiply]

theorem trace_twoBlocks (A : Matrix m m ℂ) (B : Matrix m p ℂ) (C : Matrix p m ℂ)
    (D : Matrix p p ℂ) : trace (fromBlocks A B C D) = trace A + trace D := by
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem tangentBlock_mul (X Y : Matrix m p ℂ) :
    tangentBlock X * tangentBlock Y = fromBlocks (X * Yᴴ) 0 0 (Xᴴ * Y) := by
  simp [tangentBlock, fromBlocks_multiply]

theorem tangentBlock_commutator (X Y : Matrix m p ℂ) :
    tangentBlock X * tangentBlock Y - tangentBlock Y * tangentBlock X =
      fromBlocks (X * Yᴴ - Y * Xᴴ) 0 0 (Xᴴ * Y - Yᴴ * X) := by
  rw [tangentBlock_mul, tangentBlock_mul]
  ext (i | i) (j | j) <;> simp

theorem trace_adjoint_left (X Y : Matrix m p ℂ) :
    trace (Xᴴ * Y) = star (trace (X * Yᴴ)) := by
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, trace_mul_comm]

theorem trace_adjoint_right (X Y : Matrix m p ℂ) :
    trace (Y * Xᴴ) = star (trace (X * Yᴴ)) := by
  rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- **Metric in block form**: `g(V, W) = ½ Tr(V W) = Re Tr(X Y†)`. -/
theorem metric_block (X Y : Matrix m p ℂ) :
    (trace (tangentBlock X * tangentBlock Y)).re / 2 = (trace (X * Yᴴ)).re := by
  rw [tangentBlock_mul, trace_twoBlocks, trace_adjoint_left, Complex.add_re, Complex.star_def,
    Complex.conj_re]
  ring

/-- **Curvature in block form**: `Ω(V, W) = i Tr(P [V, W]) = −2 Im Tr(X Y†)`. -/
theorem curvature_block (X Y : Matrix m p ℂ) :
    I * trace (occ * (tangentBlock X * tangentBlock Y - tangentBlock Y * tangentBlock X)) =
      -2 * ((trace (X * Yᴴ)).im : ℂ) := by
  rw [tangentBlock_commutator]
  simp only [occ, fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero,
    add_zero, zero_add]
  rw [trace_twoBlocks, trace_sub, trace_adjoint_right, Matrix.trace_zero, add_zero]
  apply Complex.ext <;> simp [Complex.star_def] <;> ring

/-- The Hermitian form reads the upper block: `Q(V, W) = Tr(P V† W) = Tr(X Y†)`. -/
theorem hermitian_form_block (X Y : Matrix m p ℂ) :
    trace (occ * (tangentBlock X)ᴴ * tangentBlock Y) = trace (X * Yᴴ) := by
  rw [tangentBlock_conjTranspose, Matrix.mul_assoc, tangentBlock_mul]
  simp only [occ, fromBlocks_multiply, Matrix.one_mul, Matrix.zero_mul, add_zero]
  rw [trace_twoBlocks, Matrix.trace_zero, add_zero]

/-- **Theorem P1, item 2**: `Q(V, W) = g(V, W) − (i/2) Ω(V, W)`. -/
theorem hermitian_form_split (X Y : Matrix m p ℂ) :
    trace (occ * (tangentBlock X)ᴴ * tangentBlock Y) =
      (((trace (tangentBlock X * tangentBlock Y)).re / 2 : ℝ) : ℂ) -
        I / 2 * (I * trace (occ * (tangentBlock X * tangentBlock Y - tangentBlock Y * tangentBlock X))) := by
  rw [hermitian_form_block, metric_block, curvature_block]
  apply Complex.ext <;> simp <;> ring

end DiracTime.ProjectorBlocks
