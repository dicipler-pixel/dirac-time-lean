import Mathlib

/-! Finite-dimensional overlap analysis. No spacetime or field-equation claims.
The local constant real trace is explicit; for a continuous family of finite
idempotents it follows from local constancy of integer-valued rank (written proof).
The principal theorem needs only entrywise differentiability at the base point.
-/
set_option autoImplicit false
noncomputable section
open Filter Matrix
open scoped Topology
namespace GravityOverlap

variable {n : Type*} [Fintype n]

def overlap (P Q : Matrix n n ℂ) : ℝ := (P * Q).trace.re
def metric (D : Matrix n n ℂ) : ℝ := (D * D).trace.re / 2

/-- Exact finite-difference identity for two idempotents of equal real trace. -/
theorem overlap_exact (P Q : Matrix n n ℂ) (k : ℝ)
    (hP : P * P = P) (hQ : Q * Q = Q)
    (htrP : P.trace.re = k) (htrQ : Q.trace.re = k) :
    overlap P Q = k - ((Q-P)*(Q-P)).trace.re / 2 := by
  have h : ((Q-P)*(Q-P)).trace = Q.trace - (P*Q).trace - (P*Q).trace + P.trace := by
    rw [sub_mul, mul_sub, mul_sub, trace_sub, trace_sub, trace_sub, hP, hQ,
      trace_mul_comm Q P]
    ring
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.sub_re, htrP, htrQ] at hr
  unfold overlap
  linarith

/-- Differentiability supplies convergence of the normalized difference square. -/
theorem difference_square_limit (P : ℝ → Matrix n n ℂ) (D : Matrix n n ℂ)
    (hd : ∀ i j, HasDerivAt (fun t => P t i j) (D i j) 0) :
    Tendsto (fun t : ℝ =>
      (((t⁻¹ • (P t-P 0)) * (t⁻¹ • (P t-P 0))).trace).re)
      (𝓝[≠] 0) (𝓝 ((D*D).trace.re)) := by
  have hs (i j : n) : Tendsto (fun t : ℝ => (t⁻¹ • (P t-P 0)) i j)
      (𝓝[≠] 0) (𝓝 (D i j)) := by
    simpa using (hd i j).tendsto_slope_zero
  have hh : Tendsto (fun t : ℝ =>
      ((t⁻¹ • (P t-P 0)) * (t⁻¹ • (P t-P 0))).trace)
      (𝓝[≠] 0) (𝓝 ((D*D).trace)) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact tendsto_finsetSum _ (fun i _ =>
      tendsto_finsetSum _ (fun j _ => (hs i j).mul (hs j i)))
  exact Complex.continuous_re.continuousAt.tendsto.comp hh

/-- The full quadratic overlap limit, obtained without a second derivative. -/
theorem overlap_quadratic_limit (P : ℝ → Matrix n n ℂ) (D : Matrix n n ℂ) (k : ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => P t i j) (D i j) 0)
    (hP0 : P 0 * P 0 = P 0) (htr0 : (P 0).trace.re = k)
    (hP : ∀ᶠ t in 𝓝 (0:ℝ), P t * P t = P t)
    (htr : ∀ᶠ t in 𝓝 (0:ℝ), (P t).trace.re = k) :
    Tendsto (fun t : ℝ => (overlap (P 0) (P t)-k)/t^2)
      (𝓝[≠] 0) (𝓝 (-metric D)) := by
  have hl := ((difference_square_limit P D hd).neg).div_const 2
  change Tendsto _ _ (𝓝 (-((D*D).trace.re / 2)))
  have he : (fun t : ℝ => (overlap (P 0) (P t)-k)/t^2) =ᶠ[𝓝[≠] 0]
      (fun t : ℝ => -(((t⁻¹ • (P t-P 0))*(t⁻¹ • (P t-P 0))).trace).re / 2) := by
    filter_upwards [hP.filter_mono nhdsWithin_le_nhds,
      htr.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t hp hq ht
    have ht0 : t ≠ 0 := by simpa using ht
    rw [overlap_exact (P 0) (P t) k hP0 hp htr0 hq]
    simp only [smul_mul_smul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
    field_simp
    ring
  simpa only [neg_div] using hl.congr' he.symm

/-- Quantified small-o remainder: every positive quadratic tolerance is attained. -/
theorem overlap_remainder_bound (P : ℝ → Matrix n n ℂ) (D : Matrix n n ℂ) (k : ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => P t i j) (D i j) 0)
    (hP0 : P 0 * P 0 = P 0) (htr0 : (P 0).trace.re = k)
    (hP : ∀ᶠ t in 𝓝 (0:ℝ), P t * P t = P t)
    (htr : ∀ᶠ t in 𝓝 (0:ℝ), (P t).trace.re = k)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t in 𝓝[≠] (0:ℝ),
      |overlap (P 0) (P t)-k+metric D*t^2| < ε*t^2 := by
  have hl := (overlap_quadratic_limit P D k hd hP0 htr0 hP htr).add_const (metric D)
  have hl0 : Tendsto (fun t : ℝ => (overlap (P 0) (P t)-k)/t^2+metric D)
      (𝓝[≠] 0) (𝓝 0) := by simpa using hl
  have he := (Metric.tendsto_nhds.mp hl0) ε hε
  filter_upwards [he, self_mem_nhdsWithin] with t he ht
  have ht0 : t ≠ 0 := by simpa using ht
  have hp : 0 < t^2 := sq_pos_of_ne_zero ht0
  have hid : (overlap (P 0) (P t)-k)/t^2+metric D =
      (overlap (P 0) (P t)-k+metric D*t^2)/t^2 := by field_simp
  simp only [Real.dist_eq, sub_zero, hid, abs_div, abs_of_pos hp] at he
  exact (div_lt_iff₀ hp).mp he

/-- A negative tangent trace form forces cap excess on both sides of zero. -/
theorem negative_direction_exceeds_cap (P : ℝ → Matrix n n ℂ) (D : Matrix n n ℂ) (k : ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => P t i j) (D i j) 0)
    (hP0 : P 0 * P 0 = P 0) (htr0 : (P 0).trace.re = k)
    (hP : ∀ᶠ t in 𝓝 (0:ℝ), P t * P t = P t)
    (htr : ∀ᶠ t in 𝓝 (0:ℝ), (P t).trace.re = k)
    (hg : metric D < 0) :
    ∀ᶠ t in 𝓝[≠] (0:ℝ), k < overlap (P 0) (P t) := by
  have hl := overlap_quadratic_limit P D k hd hP0 htr0 hP htr
  have he := hl.eventually (lt_mem_nhds (show 0 < -metric D by linarith))
  filter_upwards [he, self_mem_nhdsWithin] with t he ht
  have ht0 : t ≠ 0 := by simpa using ht
  have hp : 0 < t^2 := sq_pos_of_ne_zero ht0
  have := (lt_div_iff₀ hp).mp he
  linarith

/-- A local upper overlap cap requires a nonnegative tangent trace form. -/
theorem local_cap_requires_nonnegative (P : ℝ → Matrix n n ℂ) (D : Matrix n n ℂ) (k : ℝ)
    (hd : ∀ i j, HasDerivAt (fun t => P t i j) (D i j) 0)
    (hP0 : P 0 * P 0 = P 0) (htr0 : (P 0).trace.re = k)
    (hP : ∀ᶠ t in 𝓝 (0:ℝ), P t * P t = P t)
    (htr : ∀ᶠ t in 𝓝 (0:ℝ), (P t).trace.re = k)
    (hcap : ∀ᶠ t in 𝓝[≠] (0:ℝ), overlap (P 0) (P t) ≤ k) :
    0 ≤ metric D := by
  by_contra hn
  have he := negative_direction_exceeds_cap P D k hd hP0 htr0 hP htr (lt_of_not_ge hn)
  obtain ⟨t, ht, hc⟩ := (he.and hcap).exists
  exact (not_lt_of_ge hc) ht

/-- Requested C² specialization; differentiability alone was enough above. -/
theorem c2_overlap_limit (P : ℝ → Matrix n n ℂ) (k : ℝ)
    (hc2 : ∀ i j, ContDiffAt ℝ 2 (fun t => P t i j) 0)
    (hP0 : P 0 * P 0 = P 0) (htr0 : (P 0).trace.re = k)
    (hP : ∀ᶠ t in 𝓝 (0:ℝ), P t * P t = P t)
    (htr : ∀ᶠ t in 𝓝 (0:ℝ), (P t).trace.re = k) :
    Tendsto (fun t : ℝ => (overlap (P 0) (P t)-k)/t^2)
      (𝓝[≠] 0) (𝓝 (-metric (fun i j => deriv (fun t => P t i j) 0))) := by
  apply overlap_quadratic_limit P _ k _ hP0 htr0 hP htr
  intro i j
  exact ((hc2 i j).differentiableAt (by norm_num)).hasDerivAt

end GravityOverlap
