import Mathlib

/-!
# Finite label-preserving boundary ledger

Generic finite positive inverse-denominator bookkeeping used by the elemental
revision.  The statements are scalar quadratic-form coefficients and do not
assert a physical interpretation of the labels.
-/

namespace ElementalFoundations

noncomputable section

section FiniteLedger
variable {ι : Type*} [Fintype ι]

/-- Sum of positive boundary contributions with individually retained
positive denominator labels. -/
def resolvedLedger (w d : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i, w i / (d i - z)

/-- The same contributions after replacing all denominator labels by one
common lower floor. -/
def commonFloorLedger (w : ι → ℝ) (d₀ z : ℝ) : ℝ :=
  ∑ i, w i / (d₀ - z)

/-- Pointwise larger positive denominators can only lower a nonnegative
resolved inverse-denominator ledger. -/
theorem resolvedLedger_antitone
    (w d₁ d₂ : ι → ℝ) (z : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i, z < d₁ i)
    (hd : ∀ i, d₁ i ≤ d₂ i) :
    resolvedLedger w d₂ z ≤ resolvedLedger w d₁ z := by
  unfold resolvedLedger
  apply Finset.sum_le_sum
  intro i hi
  have h1 : 0 < d₁ i - z := sub_pos.mpr (hz i)
  have h2 : 0 < d₂ i - z := by
    have : z < d₂ i := lt_of_lt_of_le (hz i) (hd i)
    exact sub_pos.mpr this
  apply (div_le_div_iff₀ h2 h1).2
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hd i) z) (hw i)

/-- Forgetting all positive denominator labels down to a common lower floor
cannot improve the upper penalty. -/
theorem resolvedLedger_le_commonFloor
    (w d : ι → ℝ) (d₀ z : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hz : z < d₀)
    (hd : ∀ i, d₀ ≤ d i) :
    resolvedLedger w d z ≤ commonFloorLedger w d₀ z := by
  unfold resolvedLedger commonFloorLedger
  apply Finset.sum_le_sum
  intro i hi
  have h0 : 0 < d₀ - z := sub_pos.mpr hz
  have h1 : 0 < d i - z := by
    have : z < d i := lt_of_lt_of_le hz (hd i)
    exact sub_pos.mpr this
  apply (div_le_div_iff₀ h1 h0).2
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hd i) z) (hw i)

/-- A quadratic-form version: nonnegative channel weights multiplied by squared
probe amplitudes preserve the same label-resolved comparison. -/
def resolvedQuadraticLedger (w d q : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i, (w i * (q i)^2) / (d i - z)

/-- Common-floor quadratic comparison corresponding to `resolvedQuadraticLedger`. -/
def commonFloorQuadraticLedger (w q : ι → ℝ) (d₀ z : ℝ) : ℝ :=
  ∑ i, (w i * (q i)^2) / (d₀ - z)

/-- Retaining denominator labels improves or matches the common-floor quadratic
comparison for every real probe vector. -/
theorem resolvedQuadraticLedger_le_commonFloor
    (w d q : ι → ℝ) (d₀ z : ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hz : z < d₀)
    (hd : ∀ i, d₀ ≤ d i) :
    resolvedQuadraticLedger w d q z ≤
      commonFloorQuadraticLedger w q d₀ z := by
  unfold resolvedQuadraticLedger commonFloorQuadraticLedger
  apply Finset.sum_le_sum
  intro i hi
  have hn : 0 ≤ w i * (q i)^2 := mul_nonneg (hw i) (sq_nonneg (q i))
  have h0 : 0 < d₀ - z := sub_pos.mpr hz
  have h1 : 0 < d i - z := by
    have : z < d i := lt_of_lt_of_le hz (hd i)
    exact sub_pos.mpr this
  apply (div_le_div_iff₀ h1 h0).2
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right (hd i) z) hn

/-- Exact aggregation identity for the common-floor scalar ledger. -/
theorem commonFloorLedger_eq_aggregate
    (w : ι → ℝ) (d₀ z : ℝ) :
    commonFloorLedger w d₀ z = (∑ i, w i) / (d₀-z) := by
  unfold commonFloorLedger
  rw [Finset.sum_div]

/-- Exact aggregation identity for the common-floor quadratic ledger. -/
theorem commonFloorQuadraticLedger_eq_aggregate
    (w q : ι → ℝ) (d₀ z : ℝ) :
    commonFloorQuadraticLedger w q d₀ z =
      (∑ i, w i * (q i)^2) / (d₀-z) := by
  unfold commonFloorQuadraticLedger
  rw [Finset.sum_div]

end FiniteLedger

end
end ElementalFoundations

#print axioms ElementalFoundations.resolvedLedger_antitone
#print axioms ElementalFoundations.resolvedLedger_le_commonFloor
#print axioms ElementalFoundations.resolvedQuadraticLedger_le_commonFloor
#print axioms ElementalFoundations.commonFloorLedger_eq_aggregate
#print axioms ElementalFoundations.commonFloorQuadraticLedger_eq_aggregate
