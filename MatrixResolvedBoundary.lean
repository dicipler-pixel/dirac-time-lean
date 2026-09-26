import CrossTheorem
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-!
# Matrix-valued energy-resolved boundary comparison

Finite-dimensional positive-semidefinite lift of the scalar closing step in
`CrossTheorem.lean`.

Each positive matrix contribution retains its own denominator label before
inversion. Replacing all labels by one common lower floor can only increase
the comparison penalty in PSD order. This is the exact finite matrix step used
in the written energy-resolved Yang--Mills certificate. It does not formalize
Peter--Weyl completeness, Haar integration, the infinite hidden Hamiltonian, or
Schur/Feshbach spectral transfer.
-/

open Matrix
open scoped MatrixOrder

namespace YangMillsCrossTheorem

noncomputable section

variable {ι n : Type*} [Fintype ι] [Fintype n]

/-- Positive matrix contributions with their individual energy denominators. -/
def resolvedMatrixPenalty
    (M : ι → Matrix n n ℝ) (energy : ι → ℝ)
    (s offset z : ℝ) : Matrix n n ℝ :=
  ∑ i, (1 / (s * energy i + offset - z)) • M i

/-- The same matrix contributions after all denominator labels are replaced by
one common lower energy floor `c`. -/
def commonFloorMatrixPenalty
    (M : ι → Matrix n n ℝ) (s c offset z : ℝ) : Matrix n n ℝ :=
  ∑ i, (1 / (s * c + offset - z)) • M i

/-- Difference between the common-floor penalty and the energy-resolved
penalty, written contribution by contribution. -/
def matrixPenaltyGap
    (M : ι → Matrix n n ℝ) (energy : ι → ℝ)
    (s c offset z : ℝ) : Matrix n n ℝ :=
  ∑ i,
    (1 / (s * c + offset - z) -
      1 / (s * energy i + offset - z)) • M i

/-- Every coefficient in the resolved-vs-floor gap is nonnegative under the
same hypotheses as the scalar closing theorem. -/
theorem matrix_penalty_gap_coefficient_nonnegative
    (energy : ℝ) (s c offset z : ℝ)
    (hs : 0 ≤ s) (he : c ≤ energy)
    (hz : z < s*c+offset) :
    0 ≤ 1 / (s*c+offset-z) - 1 / (s*energy+offset-z) := by
  have h := resolved_term_le (1 : ℝ) s c energy offset z
    (by norm_num) hs he hz
  simpa [one_div] using sub_nonneg.mpr h

/-- The contributionwise gap is positive semidefinite for any finite family of
positive-semidefinite matrix residues. -/
theorem matrixPenaltyGap_posSemidef
    (M : ι → Matrix n n ℝ) (energy : ι → ℝ)
    (s c offset z : ℝ)
    (hM : ∀ i, (M i).PosSemidef)
    (hs : 0 ≤ s) (he : ∀ i, c ≤ energy i)
    (hz : z < s*c+offset) :
    (matrixPenaltyGap M energy s c offset z).PosSemidef := by
  unfold matrixPenaltyGap
  apply Matrix.posSemidef_sum Finset.univ
  intro i hi
  apply (hM i).smul
  exact matrix_penalty_gap_coefficient_nonnegative (energy i) s c offset z
    hs (he i) hz

/-- The difference of the two finite matrix penalties is exactly the
contributionwise PSD gap. -/
theorem commonFloor_sub_resolved_eq_gap
    (M : ι → Matrix n n ℝ) (energy : ι → ℝ)
    (s c offset z : ℝ) :
    commonFloorMatrixPenalty M s c offset z -
      resolvedMatrixPenalty M energy s offset z =
      matrixPenaltyGap M energy s c offset z := by
  unfold commonFloorMatrixPenalty resolvedMatrixPenalty matrixPenaltyGap
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sub_smul]

/-- Energy-resolved positive matrix penalties improve or match the common-floor
comparison in PSD order. Equivalently, the common-floor penalty minus the
resolved penalty is positive semidefinite. -/
theorem commonFloor_sub_resolved_posSemidef
    (M : ι → Matrix n n ℝ) (energy : ι → ℝ)
    (s c offset z : ℝ)
    (hM : ∀ i, (M i).PosSemidef)
    (hs : 0 ≤ s) (he : ∀ i, c ≤ energy i)
    (hz : z < s*c+offset) :
    (commonFloorMatrixPenalty M s c offset z -
      resolvedMatrixPenalty M energy s offset z).PosSemidef := by
  rw [commonFloor_sub_resolved_eq_gap]
  exact matrixPenaltyGap_posSemidef M energy s c offset z hM hs he hz

/-- Native matrix-order form of the result: the energy-resolved penalty is no
larger than the common-floor penalty. -/
theorem resolvedMatrixPenalty_le_commonFloor
    (M : ι → Matrix n n ℝ) (energy : ι → ℝ)
    (s c offset z : ℝ)
    (hM : ∀ i, (M i).PosSemidef)
    (hs : 0 ≤ s) (he : ∀ i, c ≤ energy i)
    (hz : z < s*c+offset) :
    resolvedMatrixPenalty M energy s offset z ≤
      commonFloorMatrixPenalty M s c offset z := by
  change (commonFloorMatrixPenalty M s c offset z -
    resolvedMatrixPenalty M energy s offset z).PosSemidef
  exact commonFloor_sub_resolved_posSemidef
    M energy s c offset z hM hs he hz

end

end YangMillsCrossTheorem

#print axioms YangMillsCrossTheorem.matrix_penalty_gap_coefficient_nonnegative
#print axioms YangMillsCrossTheorem.matrixPenaltyGap_posSemidef
#print axioms YangMillsCrossTheorem.commonFloor_sub_resolved_eq_gap
#print axioms YangMillsCrossTheorem.commonFloor_sub_resolved_posSemidef
#print axioms YangMillsCrossTheorem.resolvedMatrixPenalty_le_commonFloor
