import Mathlib

/-! Finite algebra supporting The Ledger Outlives the Metric.
These proofs do not identify the trace form with a spacetime metric or prove
Einstein equations, horizon thermodynamics, or infinite-dimensional continuation.
The analytic C² overlap argument and the full tangent-space dimension theorem
are written proofs in the paper; the corresponding algebra is certified here. -/
set_option autoImplicit false
noncomputable section
namespace Gravity

section Algebra
variable {R : Type*} [Ring R]

/-- A scalar baseline commutes with every matrix, expressed with a central element. -/
theorem baseline_commutator (H A c : R) (hc : c*A=A*c) :
    (H+c)*A-A*(H+c)=H*A-A*H := by
  noncomm_ring [hc]

/-- Tangency to the idempotent equation implies the occupied diagonal block vanishes. -/
theorem tangent_occupied_block (P D : R) (hP : P*P=P) (hD : P*D+D*P=D) :
    P*D*P=0 := by
  have h := congrArg (fun X : R => P*X) hD
  have he : P*(P*D+D*P)=P*D+P*D*P := by
    rw [mul_add, ← mul_assoc P P D, hP, ← mul_assoc]
  rw [he] at h
  exact add_left_cancel (show P*D+P*D*P=P*D+0 by simpa using h)

/-- The complementary diagonal block also vanishes. -/
theorem tangent_empty_block (P D : R) (hP : P*P=P) (hD : P*D+D*P=D) :
    (1-P)*D*(1-P)=0 := by
  have hz := tangent_occupied_block P D hP hD
  calc
    (1-P)*D*(1-P) = D-(P*D+D*P)+P*D*P := by noncomm_ring
    _ = 0 := by rw [hD,hz]; simp

/-- Every idempotent tangent has precisely its two off-diagonal blocks. -/
theorem tangent_split (P D : R) (hP : P*P=P) (hD : P*D+D*P=D) :
    D=P*D*(1-P)+(1-P)*D*P := by
  have hz := tangent_occupied_block P D hP hD
  calc
    D = P*D+D*P := hD.symm
    _ = P*D+D*P-(P*D*P+P*D*P) := by rw [hz]; simp
    _ = P*D*(1-P)+(1-P)*D*P := by noncomm_ring
end Algebra

/-- Real coordinates of Re((a+ib)(c+id)) in positive/negative square coordinates. -/
theorem neutral_square_decomposition (a b c d : ℝ) :
    a*c-b*d=((a+c)/2)^2+((b-d)/2)^2-((a-c)/2)^2-((b+d)/2)^2 := by ring

/-- The signed-square coordinate change is invertible, so no directions are lost. -/
theorem neutral_coordinate_inverse (a b c d : ℝ) :
    (a+c)/2+(a-c)/2=a ∧ (b-d)/2+(b+d)/2=b ∧
    (a+c)/2-(a-c)/2=c ∧ (b+d)/2-(b-d)/2=d := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- Entrywise identity extends to every finite collection of cross-block entries. -/
theorem neutral_finite_sum {ι : Type*} [Fintype ι] (a b c d : ι → ℝ) :
    (∑ j, (a j*c j-b j*d j)) =
    ∑ j, (((a j+c j)/2)^2+((b j-d j)/2)^2-
      ((a j-c j)/2)^2-((b j+d j)/2)^2) := by
  apply Finset.sum_congr rfl
  intro j _
  exact neutral_square_decomposition _ _ _ _

/-- Hermitian tangent slice Y=X† gives a sum of nonnegative squares. -/
theorem hermitian_slice_nonnegative (a b : ℝ) : 0 ≤ a*a-b*(-b) := by
  nlinarith [sq_nonneg a, sq_nonneg b]

/-- Reciprocal single-partner real metric determinant is a negative square. -/
theorem reciprocal_determinant (a b c d : ℝ) :
    (a^2-b^2)*(c^2-d^2)-(a*c-b*d)^2=-(a*d-b*c)^2 := by ring

theorem reciprocal_not_definite (a b c d : ℝ) :
    (a^2-b^2)*(c^2-d^2)-(a*c-b*d)^2 ≤ 0 := by
  rw [reciprocal_determinant]
  exact neg_nonpos.mpr (sq_nonneg _)

/-- Phase alignment can give rank zero, not only rank one. -/
theorem reciprocal_rank_zero_example :
    (1:ℝ)^2-1^2=0 ∧ (2:ℝ)^2-2^2=0 ∧ (1:ℝ)*2-1*2=0 := by norm_num

/-- With a positive first diagonal, the curvature-proxy determinant bound also
forces the other diagonal nonnegative. The positive-first-diagonal hypothesis matters. -/
theorem proxy_second_diagonal (a b c omega : ℝ) (ha : 0<a)
    (h : omega^2 ≤ 4*(a*c-b^2)) : 0 ≤ c := by
  have hac : 0 ≤ a*c := by nlinarith [sq_nonneg omega, sq_nonneg b]
  exact nonneg_of_mul_nonneg_left (by simpa only [mul_comm] using hac) ha

/-- Diag(0,-1) disproves the weakened PSD criterion with only a≥0. -/
theorem proxy_missing_diagonal_counterexample :
    (0:ℝ) ≤ 0 ∧ (0:ℝ)^2 ≤ 4*(0*(-1)-0^2) ∧ ¬ (0:ℝ) ≤ -1 := by norm_num

/-- Quantitative local-cap step: a negative quadratic coefficient dominates a
remainder bounded by half its magnitude. Analytic small-o existence is separate. -/
theorem negative_metric_cap (k g t r : ℝ) (hg : g<0) (ht : t≠0)
    (hr : |r| ≤ (-g/2)*t^2) : k < k-g*t^2+r := by
  have hp : 0<t^2 := sq_pos_of_ne_zero ht
  have hlo := (abs_le.mp hr).1
  have hprod : 0<(-g/2)*t^2 := mul_pos (by linarith) hp
  nlinarith

/-- Trace constraints obtained from twice differentiating P²=P. -/
theorem second_jet_trace (pdd dd trdd : ℝ)
    (hjet : 2*pdd+2*dd=trdd) (hconstantRank : trdd=0) : pdd=-dd := by linarith

/-- Hermitian and anti-Hermitian tangent sectors have an even mixing polynomial. -/
theorem mixing_quadratic (a b cross k : ℝ) (hc : cross=0) :
    a+2*k*cross-k^2*b=a-k^2*b := by rw [hc]; ring

/-- Exact determinant of a diagonal metric in the varying-projector model. -/
theorem moving_metric_determinant (y s : ℝ) :
    (1/s^2)*(-2*y/s^2)=-2*y/s^4 := by ring

theorem moving_metric_positive_side (y s : ℝ) (hy : y<0) (hs : s≠0) :
    0<1/s^2 ∧ 0<(-2*y)/s^2 := by
  have hp : 0<s^2 := sq_pos_of_ne_zero hs
  constructor
  · exact div_pos zero_lt_one hp
  · exact div_pos (by linarith) hp

theorem moving_metric_indefinite_side (y s : ℝ) (hy : 0<y) (hs : s≠0) :
    0<1/s^2 ∧ (-2*y)/s^2<0 := by
  have hp : 0<s^2 := sq_pos_of_ne_zero hs
  constructor
  · exact div_pos zero_lt_one hp
  · exact div_neg_of_neg_of_pos (by linarith) hp

open Matrix
abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ
def pointP : M2 := !![1,0;0,0]
def pointD : M2 := !![0,1;-1,0]

/-- A self-adjoint projector at one point can have a negative non-self-adjoint tangent. -/
theorem selfadjoint_point_negative_tangent :
    pointP*pointP=pointP ∧ pointP.transpose=pointP ∧
    pointP*pointD+pointD*pointP=pointD ∧ (pointD*pointD).trace/2 = -1 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [pointP,Matrix.mul_apply,Fin.sum_univ_two]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [pointP,Matrix.transpose_apply]
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [pointP,pointD,Matrix.mul_apply,Fin.sum_univ_two]
  · norm_num [pointD,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]

/-- Universal rank-one chart over the complex field used by the moving-wall example. -/
def chartP (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![1/(1+z*w),w/(1+z*w);z/(1+z*w),z*w/(1+z*w)]

theorem chart_idempotent (z w : ℂ) (h : 1+z*w≠0) : chartP z w*chartP z w=chartP z w := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [chartP,Matrix.mul_apply,Fin.sum_univ_two] <;> field_simp <;> ring

theorem chart_trace_one (z w : ℂ) (h : 1+z*w≠0) : (chartP z w).trace=1 := by
  simp [chartP,Matrix.trace,Fin.sum_univ_two]
  field_simp

theorem chart_overlap (z w Z W : ℂ) (h : 1+z*w≠0) (h' : 1+Z*W≠0) :
    (chartP z w*chartP Z W).trace=(1+w*Z)*(1+W*z)/((1+z*w)*(1+Z*W)) := by
  simp [chartP,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two]
  field_simp
  <;> ring
end Gravity
