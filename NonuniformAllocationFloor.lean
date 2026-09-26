import SchurFloorTransfer

/-!
# Nonuniform local allocation -> global lower floor

This module isolates the exact finite bookkeeping statement used when a
nonnegative electric/resource term is distributed across overlapping local
cells with nonuniform coefficients.

The theorem is deliberately stated at the scalar/quadratic-form level.  In a
matrix or operator application, fix a test vector and read `energy i`,
`potential c`, and `localFloor c` as the corresponding quadratic-form values.
If the cellwise lower bounds hold for every vector, the same inequality lifts
pointwise to the operator lower bound.

No equal allocation and no disjoint partition of cells is required.  The only
capacity condition is that the total coefficient charged against each
nonnegative global energy term is at most one.

This is finite algebra.  It does not establish the physical Yang--Mills local
floor hypotheses, a volume-uniform gap, a continuum limit, or
Osterwalder--Schrader reconstruction.
-/

open scoped BigOperators

namespace CrossTheorem

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The total energy charged to all local cells is bounded by the original
nonnegative global energy whenever each global component is charged with total
coefficient at most one.  Coefficients may be completely nonuniform and cells
may overlap. -/
theorem allocation_weighted_energy_le_total
    (energy : ι → ℝ) (alloc : κ → ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hcap : ∀ i, (∑ c, alloc c i) ≤ 1) :
    (∑ c, ∑ i, alloc c i * energy i) ≤ ∑ i, energy i := by
  calc
    (∑ c, ∑ i, alloc c i * energy i)
        = ∑ i, (∑ c, alloc c i) * energy i := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
    _ ≤ ∑ i, energy i := by
      apply Finset.sum_le_sum
      intro i _
      have h := mul_le_mul_of_nonneg_right (hcap i) (henergy i)
      simpa using h

/-- **Nonuniform allocation floor.**  If every local cell has certified lower
floor `localFloor c` after receiving its chosen shares of the global energy,
then the sum of those local floors is a valid lower bound for the full
potential-plus-energy quantity.  Equal sharing and disjoint cells are not
assumptions. -/
theorem nonuniform_allocation_global_floor
    (energy : ι → ℝ)
    (potential localFloor : κ → ℝ)
    (alloc : κ → ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hcap : ∀ i, (∑ c, alloc c i) ≤ 1)
    (hlocal : ∀ c,
      localFloor c ≤ potential c + ∑ i, alloc c i * energy i) :
    (∑ c, localFloor c) ≤ (∑ c, potential c) + ∑ i, energy i := by
  calc
    (∑ c, localFloor c)
        ≤ ∑ c, (potential c + ∑ i, alloc c i * energy i) := by
            exact Finset.sum_le_sum (fun c _ => hlocal c)
    _ = (∑ c, potential c) + ∑ c, ∑ i, alloc c i * energy i := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ c, potential c) + ∑ i, energy i := by
          have h := allocation_weighted_energy_le_total energy alloc henergy hcap
          linarith

/-- Equivalent residual form of the global floor certificate. -/
theorem nonuniform_allocation_residual_nonnegative
    (energy : ι → ℝ)
    (potential localFloor : κ → ℝ)
    (alloc : κ → ι → ℝ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hcap : ∀ i, (∑ c, alloc c i) ≤ 1)
    (hlocal : ∀ c,
      localFloor c ≤ potential c + ∑ i, alloc c i * energy i) :
    0 ≤ ((∑ c, potential c) + ∑ i, energy i) - ∑ c, localFloor c := by
  exact sub_nonneg.mpr
    (nonuniform_allocation_global_floor energy potential localFloor alloc
      henergy hcap hlocal)

end CrossTheorem

#print axioms CrossTheorem.allocation_weighted_energy_le_total
#print axioms CrossTheorem.nonuniform_allocation_global_floor
#print axioms CrossTheorem.nonuniform_allocation_residual_nonnegative
