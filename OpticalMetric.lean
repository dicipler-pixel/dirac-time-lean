import Mathlib

/-!
LIGHT-CONSTITUTIVE-02: candidate algebraic constituents.
STATUS: compilation tracked in evidence/report.json for this revision.
These declarations do not certify the spectral differentiation or Maxwell model.
Physical hypotheses remain in the accompanying written proof.
-/
set_option autoImplicit false
noncomputable section

namespace LightConstitutive

/-- A one-transition field metric in a fixed real polarization. -/
def transitionMetric (amplitude gap : ℝ) : ℝ := amplitude ^ 2 / gap ^ 2

/-- Lossless polarizability in that polarization. The physical domain excludes poles. -/
def polarizability (amplitude gap photonEnergy : ℝ) : ℝ :=
  2 * gap * amplitude ^ 2 / (gap ^ 2 - photonEnergy ^ 2)

/-- The energy weight multiplying the field-driven projector metric. -/
def responseWeight (gap photonEnergy : ℝ) : ℝ :=
  2 * gap ^ 3 / (gap ^ 2 - photonEnergy ^ 2)

theorem response_is_weighted_metric (a gap x : ℝ)
    (hg : gap ≠ 0) (hd : gap ^ 2 - x ^ 2 ≠ 0) :
    polarizability a gap x = responseWeight gap x * transitionMetric a gap := by
  unfold polarizability responseWeight transitionMetric
  field_simp [hg, hd]
  <;> ring

/-- State the physically necessary subgap condition before using positivity. -/
theorem response_weight_positive (gap x : ℝ)
    (hg : 0 < gap) (hx : x ^ 2 < gap ^ 2) :
    0 < responseWeight gap x := by
  unfold responseWeight
  exact div_pos (mul_pos (by norm_num) (pow_pos hg 3)) (sub_pos.mpr hx)

theorem static_response (a gap : ℝ) (hg : gap ≠ 0) :
    polarizability a gap 0 = (2 * gap) * transitionMetric a gap := by
  unfold polarizability transitionMetric
  ring

section FiniteChannels
variable {ι : Type*} [Fintype ι]

def gramForm (q : ι → ℝ) : ℝ := ∑ i, (q i) ^ 2

def weightedForm (w q : ι → ℝ) : ℝ := ∑ i, w i * (q i) ^ 2

/-- A positive reweighting cannot create a null direction. -/
theorem weighted_zero_iff (w q : ι → ℝ) (hw : ∀ i, 0 < w i) :
    weightedForm w q = 0 ↔ ∀ i, q i = 0 := by
  classical
  constructor
  · intro h i
    have hle : w i * (q i) ^ 2 ≤ ∑ j, w j * (q j) ^ 2 := by
      simpa using (Finset.single_le_sum (s := Finset.univ)
        (f := fun j => w j * (q j) ^ 2)
        (fun j hj => mul_nonneg (le_of_lt (hw j)) (sq_nonneg (q j)))
        (Finset.mem_univ i))
    change w i * (q i) ^ 2 ≤ weightedForm w q at hle
    rw [h] at hle
    have hz : w i * (q i) ^ 2 = 0 :=
      le_antisymm hle (mul_nonneg (le_of_lt (hw i)) (sq_nonneg (q i)))
    have hs : (q i) ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw i))
    nlinarith
  · intro h
    simp [weightedForm, h]

theorem gram_zero_iff (q : ι → ℝ) : gramForm q = 0 ↔ ∀ i, q i = 0 := by
  simpa [gramForm, weightedForm] using
    (weighted_zero_iff (fun _ : ι => (1 : ℝ)) q (by intro i; norm_num))

theorem matching_null_directions (w q : ι → ℝ) (hw : ∀ i, 0 < w i) :
    weightedForm w q = 0 ↔ gramForm q = 0 := by
  rw [weighted_zero_iff w q hw, gram_zero_iff q]

theorem response_lower_bound (w q : ι → ℝ) (lo : ℝ) (hw : ∀ i, lo ≤ w i) :
    lo * gramForm q ≤ weightedForm w q := by
  unfold gramForm weightedForm
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hw i) (sq_nonneg (q i)))

theorem response_upper_bound (w q : ι → ℝ) (hi : ℝ) (hw : ∀ i, w i ≤ hi) :
    weightedForm w q ≤ hi * gramForm q := by
  unfold gramForm weightedForm
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i hi' => mul_le_mul_of_nonneg_right (hw i) (sq_nonneg (q i)))

/-- Equal excitation gaps factor out exactly. -/
theorem constant_gap_factor (a : ι → ℝ) (gap x : ℝ)
    (hg : gap ≠ 0) (hd : gap ^ 2 - x ^ 2 ≠ 0) :
    (∑ i, polarizability (a i) gap x) =
      responseWeight gap x * ∑ i, transitionMetric (a i) gap := by
  simp_rw [response_is_weighted_metric _ gap x hg hd]
  rw [Finset.mul_sum]

end FiniteChannels

/-- y denotes squared photon energy; no square-root convention is hidden. -/
def threeLevelResponse (y : ℝ) : ℝ := 2 / (1-y) + 16 / (4-y)

theorem numerator_zero_away_from_poles :
    threeLevelResponse (4/3) = 0 ∧ (1-(4/3 : ℝ)) ≠ 0 ∧ (4-(4/3 : ℝ)) ≠ 0 := by
  norm_num [threeLevelResponse]

theorem tune_out_metric_nonzero :
    transitionMetric 1 1 + transitionMetric 2 2 = 2 := by
  norm_num [transitionMetric]

/-- Algebraic square of phase matching; this is not a Lean derivation of Maxwell's equations. -/
theorem squared_phase_matching (n1 n2 s1 s2 : ℝ) (h : n1*s1=n2*s2) :
    n1^2*s1^2=n2^2*s2^2 := by
  have hs := congrArg (fun y : ℝ => y^2) h
  nlinarith [hs]

section Peel
variable {ι : Type*} [Fintype ι]

/-- With fixed transition amplitudes, reducing nonnegative channel weights
cannot increase the response form. This is not a theorem about changing H. -/
theorem weighted_mono (a b q : ι → ℝ) (h : ∀ i, a i ≤ b i) :
    weightedForm a q ≤ weightedForm b q := by
  unfold weightedForm
  exact Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_right (h i) (sq_nonneg (q i)))

theorem weighted_nonneg (w q : ι → ℝ) (h : ∀ i, 0 ≤ w i) :
    0 ≤ weightedForm w q := by
  unfold weightedForm
  exact Finset.sum_nonneg (fun i hi => mul_nonneg (h i) (sq_nonneg (q i)))

/-- A direction already silent stays silent under removal of positive
contributions with fixed amplitudes. The converse is deliberately not claimed. -/
theorem peel_null_persists (after before q : ι → ℝ)
    (ha : ∀ i, 0 ≤ after i) (hab : ∀ i, after i ≤ before i)
    (hz : weightedForm before q = 0) : weightedForm after q = 0 := by
  apply le_antisymm
  · calc
      weightedForm after q ≤ weightedForm before q := weighted_mono after before q hab
      _ = 0 := hz
  · exact weighted_nonneg after q ha

/-- Every strictly positive reweighting has the same null directions. -/
theorem positive_reweighting_null_equivalence (a b q : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    weightedForm a q = 0 ↔ weightedForm b q = 0 := by
  rw [weighted_zero_iff a q ha, weighted_zero_iff b q hb]
end Peel

end LightConstitutive
