import UPGProjectorMetric

/-!
# Projector transport derivative -> coupling metric

This module welds the already-certified adapted-block algebra to a finite,
entrywise calculus statement.  No matrix exponential, unitarity, Hamiltonian
interpretation, electron/light identification, or spacetime geometry is
assumed.  The transport paths and their derivatives at zero are explicit
hypotheses.
-/

open Matrix
open scoped BigOperators

namespace UPGFeedback

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

private theorem hasDerivAt_matrix_mul_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (U V : ℝ → Matrix n n ℝ) (U0 V0 KU KV : Matrix n n ℝ)
    (hU0 : U 0 = U0) (hV0 : V 0 = V0)
    (hU : ∀ i j, HasDerivAt (fun t => U t i j) (KU i j) 0)
    (hV : ∀ i j, HasDerivAt (fun t => V t i j) (KV i j) 0) :
    ∀ i j,
      HasDerivAt (fun t => (U t * V t) i j)
        ((KU * V0 + U0 * KV) i j) 0 := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.add_apply]
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => (hU i k).mul (hV k j))
  simpa [hU0, hV0, Matrix.mul_apply, Finset.sum_add_distrib] using hsum

/-- A two-sided transport whose endpoint derivatives are `K` and `-K` has
first derivative `[K,P]`. -/
theorem hasDerivAt_retained_transport_commutator
    (U V : ℝ → Matrix (Sum r h) (Sum r h) ℝ)
    (K : Matrix (Sum r h) (Sum r h) ℝ)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : ∀ i j, HasDerivAt (fun t => U t i j) (K i j) 0)
    (hV : ∀ i j, HasDerivAt (fun t => V t i j) ((-K) i j) 0) :
    ∀ i j,
      HasDerivAt
        (fun t => (U t * (retainedProjection (r := r) (h := h)) * V t) i j)
        ((K * (retainedProjection (r := r) (h := h)) -
          (retainedProjection (r := r) (h := h)) * K) i j) 0 := by
  intro i j
  have hUP : ∀ a b,
      HasDerivAt
        (fun t => (U t * (retainedProjection (r := r) (h := h))) a b)
        ((K * (retainedProjection (r := r) (h := h))) a b) 0 := by
    intro a b
    have hconst : ∀ p q,
        HasDerivAt
          (fun _ : ℝ => (retainedProjection (r := r) (h := h)) p q) 0 0 := by
      intro p q
      simpa using
        (hasDerivAt_const (x := (0 : ℝ))
          (c := (retainedProjection (r := r) (h := h)) p q))
    have h := hasDerivAt_matrix_mul_sum U
      (fun _ => retainedProjection (r := r) (h := h))
      1 (retainedProjection (r := r) (h := h)) K 0 hU0 rfl hU hconst a b
    simpa using h
  have hprod := hasDerivAt_matrix_mul_sum
    (fun t => U t * (retainedProjection (r := r) (h := h))) V
    (retainedProjection (r := r) (h := h)) 1
    (K * (retainedProjection (r := r) (h := h))) (-K)
    (by simp [hU0]) hV0 hUP hV i j
  simpa [Matrix.mul_assoc, sub_eq_add_neg, Matrix.mul_neg] using hprod

/-- Specialization to the adapted block generator.  The first derivative of the
transported retained projector is exactly the previously formalized
`projectorCommutator A B D`. -/
theorem hasDerivAt_retained_transport_blockCommutator
    (U V : ℝ → Matrix (Sum r h) (Sum r h) ℝ)
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : ∀ i j,
      HasDerivAt (fun t => U t i j) (blockHamiltonian A B D i j) 0)
    (hV : ∀ i j,
      HasDerivAt (fun t => V t i j) ((-blockHamiltonian A B D) i j) 0) :
    ∀ i j,
      HasDerivAt
        (fun t => (U t * (retainedProjection (r := r) (h := h)) * V t) i j)
        (projectorCommutator A B D i j) 0 := by
  intro i j
  simpa [projectorCommutator] using
    hasDerivAt_retained_transport_commutator
      U V (blockHamiltonian A B D) hU0 hV0 hU hV i j

/-- Full finite bridge: under explicit transport derivative hypotheses, the
projector tangent is the adapted commutator, and its conventional one-half
cross-block square energy is exactly the retained-hidden coupling energy. -/
theorem retained_transport_tangent_and_metric_bridge
    (U V : ℝ → Matrix (Sum r h) (Sum r h) ℝ)
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : ∀ i j,
      HasDerivAt (fun t => U t i j) (blockHamiltonian A B D i j) 0)
    (hV : ∀ i j,
      HasDerivAt (fun t => V t i j) ((-blockHamiltonian A B D) i j) 0) :
    (∀ i j,
      HasDerivAt
        (fun t => (U t * (retainedProjection (r := r) (h := h)) * V t) i j)
        (projectorCommutator A B D i j) 0) ∧
    (1 / 2 : ℝ) * projectorCrossEnergy A B D = couplingEnergy B := by
  constructor
  · exact hasDerivAt_retained_transport_blockCommutator U V A B D hU0 hV0 hU hV
  · exact half_projectorCrossEnergy_eq_couplingEnergy A B D

end UPGFeedback

#print axioms UPGFeedback.hasDerivAt_retained_transport_commutator
#print axioms UPGFeedback.hasDerivAt_retained_transport_blockCommutator
#print axioms UPGFeedback.retained_transport_tangent_and_metric_bridge
