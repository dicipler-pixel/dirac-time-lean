import CouplingFeedback
import Mathlib.Data.Matrix.Block

/-!
# Finite projector dynamics and coupling metric

This module connects an adapted retained/hidden block generator to the tangent
of a transported projector and to the exact squared cross-block coupling.
No matrix exponential, unitarity, gauge-field identification, spacetime metric,
or continuum dynamics is assumed: the endpoint derivatives of the transport
paths are explicit hypotheses.
-/

open Matrix
open scoped BigOperators

namespace YangMillsFinite

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- Adapted real symmetric finite generator. -/
def blockGenerator (A : Matrix r r ℝ) (B : Matrix r h ℝ)
    (D : Matrix h h ℝ) : Matrix (Sum r h) (Sum r h) ℝ :=
  Matrix.fromBlocks A B B.transpose D

/-- Projector onto the retained block. -/
def retainedProjection : Matrix (Sum r h) (Sum r h) ℝ :=
  Matrix.fromBlocks 1 0 0 0

/-- Commutator of the finite generator with the retained projector. -/
def projectorCommutator (A : Matrix r r ℝ) (B : Matrix r h ℝ)
    (D : Matrix h h ℝ) : Matrix (Sum r h) (Sum r h) ℝ :=
  blockGenerator A B D * retainedProjection -
    retainedProjection * blockGenerator A B D

/-- Exact block form of the commutator. -/
theorem projectorCommutator_eq_blocks
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCommutator A B D = Matrix.fromBlocks 0 (-B) B.transpose 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [projectorCommutator, blockGenerator, retainedProjection,
      Matrix.fromBlocks_multiply]

/-- Projector commutation is exactly absence of retained/hidden coupling. -/
theorem projectorCommutator_eq_zero_iff
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCommutator A B D = 0 ↔ B = 0 := by
  constructor
  · intro hC
    have hblocks := projectorCommutator_eq_blocks A B D
    rw [hC] at hblocks
    ext i j
    have h := congrArg
      (fun M : Matrix (Sum r h) (Sum r h) ℝ => M (Sum.inl i) (Sum.inr j))
      hblocks
    simpa using h
  · intro hB
    subst B
    simpa using (projectorCommutator_eq_blocks A (0 : Matrix r h ℝ) D)

/-- Squared Frobenius energy of the rectangular coupling. -/
def couplingEnergy (B : Matrix r h ℝ) : ℝ :=
  ∑ i, ∑ j, (B i j)^2

/-- Trace of the zero-time feedback Gram equals total coupling energy. -/
theorem trace_memoryAtZero_eq_couplingEnergy (B : Matrix r h ℝ) :
    Matrix.trace (memoryAtZero B) = couplingEnergy B := by
  simp [memoryAtZero, couplingEnergy, Matrix.trace, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]

/-- Energy in both oriented cross blocks of the projector commutator. -/
def projectorCrossEnergy
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) : ℝ :=
  (∑ i : r, ∑ j : h,
      (projectorCommutator A B D (Sum.inl i) (Sum.inr j))^2) +
  (∑ i : h, ∑ j : r,
      (projectorCommutator A B D (Sum.inr i) (Sum.inl j))^2)

/-- Exact factor-of-two cross-block identity. -/
theorem projectorCrossEnergy_eq_two_mul_couplingEnergy
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    projectorCrossEnergy A B D = 2 * couplingEnergy B := by
  unfold projectorCrossEnergy
  rw [projectorCommutator_eq_blocks]
  unfold couplingEnergy
  simp only [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.neg_apply, Matrix.transpose_apply, neg_sq]
  have hswap :
      (∑ i : h, ∑ j : r, (B j i)^2) =
        ∑ i : r, ∑ j : h, (B i j)^2 := by
    rw [Finset.sum_comm]
  rw [hswap]
  ring

/-- Conventional one-half projector normalization equals coupling energy. -/
theorem half_projectorCrossEnergy_eq_couplingEnergy
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) :
    (1 / 2 : ℝ) * projectorCrossEnergy A B D = couplingEnergy B := by
  rw [projectorCrossEnergy_eq_two_mul_couplingEnergy]
  ring

private theorem hasDerivAt_matrix_mul_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : ℝ → Matrix n n ℝ) (U0 V0 KU KV : Matrix n n ℝ)
    (hU0 : U 0 = U0) (hV0 : V 0 = V0)
    (hU : ∀ (i j : n),
      HasDerivAt (fun t : ℝ => U t i j) (KU i j) (0 : ℝ))
    (hV : ∀ (i j : n),
      HasDerivAt (fun t : ℝ => V t i j) (KV i j) (0 : ℝ)) :
    ∀ (i j : n),
      HasDerivAt (fun t : ℝ => (U t * V t) i j)
        ((KU * V0 + U0 * KV) i j) (0 : ℝ) := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => (hU i k).mul (hV k j))
  simpa [hU0, hV0, Matrix.mul_apply, Finset.sum_add_distrib] using hsum

/-- A two-sided transport with derivatives `K` and `-K` has tangent `[K,P]`. -/
theorem hasDerivAt_retained_transport_commutator
    (U V : ℝ → Matrix (Sum r h) (Sum r h) ℝ)
    (K : Matrix (Sum r h) (Sum r h) ℝ)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : ∀ (i j : Sum r h),
      HasDerivAt (fun t : ℝ => U t i j) (K i j) (0 : ℝ))
    (hV : ∀ (i j : Sum r h),
      HasDerivAt (fun t : ℝ => V t i j) ((-K) i j) (0 : ℝ)) :
    ∀ (i j : Sum r h),
      HasDerivAt
        (fun t : ℝ =>
          (U t * (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) * V t) i j)
        ((K * (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) -
          (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) * K) i j)
        (0 : ℝ) := by
  intro i j
  have hUP : ∀ (a b : Sum r h),
      HasDerivAt
        (fun t : ℝ =>
          (U t * (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ)) a b)
        ((K * (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ)) a b)
        (0 : ℝ) := by
    intro a b
    have hconst : ∀ (p q : Sum r h),
        HasDerivAt
          (fun _ : ℝ =>
            (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) p q)
          0 (0 : ℝ) := by
      intro p q
      simpa using
        (hasDerivAt_const (x := (0 : ℝ))
          (c := (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) p q))
    have h := hasDerivAt_matrix_mul_sum U
      (fun _ : ℝ => (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ))
      1 (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) K 0
      hU0 rfl hU hconst a b
    simpa using h
  have hprod := hasDerivAt_matrix_mul_sum
    (fun t : ℝ =>
      U t * (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ))
    V (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) 1
    (K * (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ)) (-K)
    (by simp [hU0]) hV0 hUP hV i j
  simpa [Matrix.mul_assoc, sub_eq_add_neg, Matrix.mul_neg] using hprod

/-- Full finite bridge: tangent commutator plus exact coupling metric. -/
theorem retained_transport_tangent_and_metric_bridge
    (U V : ℝ → Matrix (Sum r h) (Sum r h) ℝ)
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : ∀ (i j : Sum r h),
      HasDerivAt (fun t : ℝ => U t i j) (blockGenerator A B D i j) (0 : ℝ))
    (hV : ∀ (i j : Sum r h),
      HasDerivAt (fun t : ℝ => V t i j) ((-blockGenerator A B D) i j) (0 : ℝ)) :
    (∀ (i j : Sum r h),
      HasDerivAt
        (fun t : ℝ =>
          (U t * (retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) * V t) i j)
        (projectorCommutator A B D i j) (0 : ℝ)) ∧
    (1 / 2 : ℝ) * projectorCrossEnergy A B D = couplingEnergy B := by
  constructor
  · intro i j
    simpa [projectorCommutator] using
      hasDerivAt_retained_transport_commutator
        U V (blockGenerator A B D) hU0 hV0 hU hV i j
  · exact half_projectorCrossEnergy_eq_couplingEnergy A B D

end YangMillsFinite

#print axioms YangMillsFinite.projectorCommutator_eq_blocks
#print axioms YangMillsFinite.projectorCommutator_eq_zero_iff
#print axioms YangMillsFinite.trace_memoryAtZero_eq_couplingEnergy
#print axioms YangMillsFinite.projectorCrossEnergy_eq_two_mul_couplingEnergy
#print axioms YangMillsFinite.half_projectorCrossEnergy_eq_couplingEnergy
#print axioms YangMillsFinite.hasDerivAt_retained_transport_commutator
#print axioms YangMillsFinite.retained_transport_tangent_and_metric_bridge
