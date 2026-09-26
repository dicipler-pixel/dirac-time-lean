import ProjectorDynamics
import ObservabilityKernel
import NonuniformAllocationFloor

/-!
# Longest finite Yang--Mills operator-first chain

This file deliberately recombines the previously separated certified finite
lanes: projector dynamics / coupling feedback / observability from PR #51 and
the energy-resolved / Schur / nonuniform-tail / allocation floor stack from
PRs #52, #54 and #56.

The statements below are finite algebraic bridge theorems. They do not supply
the missing physical local-floor hypotheses, RG/polymer activity estimate,
volume-uniformity, thermodynamic or continuum limit, Osterwalder--Schrader
reconstruction, or the Clay Yang--Mills mass-gap theorem.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace YangMillsLongestChain

noncomputable section

/-! ## Geometry -> coupling -> feedback -/

variable {r h : Type*} [Fintype r] [Fintype h] [DecidableEq r] [DecidableEq h]

/-- If the adapted projector commutator vanishes, then the retained/hidden
coupling vanishes and hence its zero-time feedback Gram vanishes. -/
theorem commutator_zero_implies_memory_zero
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (hcomm : YangMillsFinite.projectorCommutator A B D = 0) :
    YangMillsFinite.memoryAtZero B = 0 := by
  have hB : B = 0 :=
    (YangMillsFinite.projectorCommutator_eq_zero_iff A B D).mp hcomm
  exact (YangMillsFinite.memoryAtZero_eq_zero_iff B).mpr hB

/-- In the same zero-coupling regime the Schur correction disappears exactly:
the effective retained block at a candidate floor is just the shifted retained
block. -/
theorem commutator_zero_implies_schur_reduces
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) (μ : ℝ)
    (hcomm : YangMillsFinite.projectorCommutator A B D = 0) :
    CrossTheorem.schurAtFloor A B D μ = CrossTheorem.retainedAtFloor A μ := by
  have hB : B = 0 :=
    (YangMillsFinite.projectorCommutator_eq_zero_iff A B D).mp hcomm
  subst B
  simp [CrossTheorem.schurAtFloor]

/-- The transported-projector tangent, its normalized cross energy, and the
trace of the retained feedback Gram all meet at the same coupling energy. -/
theorem transport_metric_memory_chain
    (U V : ℝ → Matrix (Sum r h) (Sum r h) ℝ)
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ)
    (hU0 : U 0 = 1) (hV0 : V 0 = 1)
    (hU : ∀ (i j : Sum r h),
      HasDerivAt (fun t : ℝ => U t i j)
        (YangMillsFinite.blockGenerator A B D i j) (0 : ℝ))
    (hV : ∀ (i j : Sum r h),
      HasDerivAt (fun t : ℝ => V t i j)
        ((-YangMillsFinite.blockGenerator A B D) i j) (0 : ℝ)) :
    (∀ (i j : Sum r h),
      HasDerivAt
        (fun t : ℝ =>
          (U t *
            (YangMillsFinite.retainedProjection : Matrix (Sum r h) (Sum r h) ℝ) *
            V t) i j)
        (YangMillsFinite.projectorCommutator A B D i j) (0 : ℝ)) ∧
    (1 / 2 : ℝ) * YangMillsFinite.projectorCrossEnergy A B D =
      YangMillsFinite.couplingEnergy B ∧
    Matrix.trace (YangMillsFinite.memoryAtZero B) =
      YangMillsFinite.couplingEnergy B := by
  have hbridge := YangMillsFinite.retained_transport_tangent_and_metric_bridge
    U V A B D hU0 hV0 hU hV
  exact ⟨hbridge.1, hbridge.2,
    YangMillsFinite.trace_memoryAtZero_eq_couplingEnergy B⟩

/-! ## Energy labels -> Schur floor -> full finite floor -/

variable {ι : Type*} [Fintype ι]

/-- Replacing a common denominator floor by positive energy-resolved matrix
penalties cannot destroy a retained PSD floor. -/
theorem resolved_penalty_preserves_retained_floor
    (A : Matrix r r ℝ) (μ : ℝ)
    (M : ι → Matrix r r ℝ) (energy : ι → ℝ)
    (s c offset z : ℝ)
    (hM : ∀ i, (M i).PosSemidef)
    (hs : 0 ≤ s) (he : ∀ i, c ≤ energy i)
    (hz : z < s*c+offset)
    (hFloor :
      (CrossTheorem.retainedAtFloor A μ -
        YangMillsCrossTheorem.commonFloorMatrixPenalty M s c offset z).PosSemidef) :
    (CrossTheorem.retainedAtFloor A μ -
      YangMillsCrossTheorem.resolvedMatrixPenalty M energy s offset z).PosSemidef := by
  have hpen := YangMillsCrossTheorem.resolvedMatrixPenalty_le_commonFloor
    M energy s c offset z hM hs he hz
  have hmono :
      CrossTheorem.retainedAtFloor A μ -
          YangMillsCrossTheorem.commonFloorMatrixPenalty M s c offset z ≤
      CrossTheorem.retainedAtFloor A μ -
          YangMillsCrossTheorem.resolvedMatrixPenalty M energy s offset z := by
    exact sub_le_sub_left hpen _
  have hzero :
      (0 : Matrix r r ℝ) ≤
        CrossTheorem.retainedAtFloor A μ -
          YangMillsCrossTheorem.commonFloorMatrixPenalty M s c offset z :=
    hFloor.nonneg
  have hout :
      (0 : Matrix r r ℝ) ≤
        CrossTheorem.retainedAtFloor A μ -
          YangMillsCrossTheorem.resolvedMatrixPenalty M energy s offset z :=
    le_trans hzero hmono
  exact hout.posSemidef

/-- The energy-resolved comparison feeds the exact finite Schur floor transfer.
The one-sided hypothesis `hResolvedLeSchur` is the load-bearing bridge: the
energy-resolved retained lower comparison lies below the actual finite Schur
complement. Equality is not required. This matches the paper's order chain
`K_res(z) <= S_H(z)` and keeps the physical comparison hypothesis explicit. -/
theorem resolved_schur_chain_to_full_floor
    (A : Matrix r r ℝ) (B : Matrix r h ℝ) (D : Matrix h h ℝ) (μ : ℝ)
    (M : ι → Matrix r r ℝ) (energy : ι → ℝ)
    (s c offset z : ℝ)
    (hM : ∀ i, (M i).PosSemidef)
    (hs : 0 ≤ s) (he : ∀ i, c ≤ energy i)
    (hz : z < s*c+offset)
    (hCommonFloor :
      (CrossTheorem.retainedAtFloor A μ -
        YangMillsCrossTheorem.commonFloorMatrixPenalty M s c offset z).PosSemidef)
    (hResolvedLeSchur :
      CrossTheorem.retainedAtFloor A μ -
          YangMillsCrossTheorem.resolvedMatrixPenalty M energy s offset z ≤
        CrossTheorem.schurAtFloor A B D μ)
    (hHidden : (CrossTheorem.hiddenAtFloor D μ).PosDef)
    [Invertible (CrossTheorem.hiddenAtFloor D μ)] :
    (CrossTheorem.symBlock A B D -
      μ • (1 : Matrix (Sum r h) (Sum r h) ℝ)).PosSemidef := by
  have hResolved := resolved_penalty_preserves_retained_floor
    A μ M energy s c offset z hM hs he hz hCommonFloor
  have hzero :
      (0 : Matrix r r ℝ) ≤
        CrossTheorem.retainedAtFloor A μ -
          YangMillsCrossTheorem.resolvedMatrixPenalty M energy s offset z :=
    hResolved.nonneg
  have hSchurOrder :
      (0 : Matrix r r ℝ) ≤ CrossTheorem.schurAtFloor A B D μ :=
    le_trans hzero hResolvedLeSchur
  have hSchur : (CrossTheorem.schurAtFloor A B D μ).PosSemidef :=
    hSchurOrder.posSemidef
  exact (CrossTheorem.full_shift_posSemidef_iff_schur
    A B D μ hHidden).mpr hSchur

/-! ## Nonuniform local floor -> overlap ledger -> surviving positive margin -/

variable {e cell tailIx budgetCell : Type*}
  [Fintype e] [Fintype cell] [Fintype tailIx] [Fintype budgetCell]
  [DecidableEq tailIx] [DecidableEq budgetCell]

/-- The longest scalar resource/tail chain currently available: nonuniform
possibly-overlapping local energy allocation first supplies a global base floor;
a second overlap-aware ledger covers heterogeneous hidden-tail budgets; if that
total budget is below the local-floor margin, a strictly positive residual
survives. -/
theorem allocation_overlap_tail_chain
    (energy0 : e → ℝ)
    (potential localFloor : cell → ℝ)
    (alloc : cell → e → ℝ)
    (tail eps : tailIx → ℝ)
    (tailAlloc : tailIx → budgetCell → ℝ)
    (cellBudget : budgetCell → ℝ)
    (henergy : ∀ i, 0 ≤ energy0 i)
    (hcap : ∀ i, (∑ c, alloc c i) ≤ 1)
    (hlocal : ∀ c,
      localFloor c ≤ potential c + ∑ i, alloc c i * energy0 i)
    (htail : ∀ i, tail i ≤ eps i)
    (hcover : ∀ i, eps i ≤ ∑ c, tailAlloc i c)
    (hcell : ∀ c, (∑ i, tailAlloc i c) ≤ cellBudget c)
    (hbudget : (∑ c, cellBudget c) < ∑ c, localFloor c) :
    0 < ((∑ c, potential c) + ∑ i, energy0 i) - ∑ i, tail i := by
  have hfloor := CrossTheorem.nonuniform_allocation_global_floor
    energy0 potential localFloor alloc henergy hcap hlocal
  have hbase :
      (∑ c, localFloor c) * (1 : ℝ) ≤
        (∑ c, potential c) + ∑ i, energy0 i := by
    simpa using hfloor
  have htail1 : ∀ i, tail i ≤ eps i * (1 : ℝ) := by
    intro i
    simpa using htail i
  exact CrossTheorem.positive_gap_of_overlap_allocation
    ((∑ c, potential c) + ∑ i, energy0 i)
    tail eps tailAlloc cellBudget (∑ c, localFloor c) 1
    (by norm_num) hbase htail1 hcover hcell hbudget

/-! ## Dual observability certificate survives a change of presentation -/

variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U]

/-- If a target functional is explicitly reconstructed from the observation,
then no hidden forcing exists; the same statement remains true after any
invertible change of state coordinates. -/
theorem dual_certificate_survives_presentation
    (A : V →ₗ[K] W) (b : V →ₗ[K] K)
    (y : W →ₗ[K] K) (hb : b = y.comp A)
    (equiv : U ≃ₗ[K] V) :
    ¬ YangMillsFinite.CanForce
      (A.comp equiv.toLinearMap) (b.comp equiv.toLinearMap) := by
  intro hforce
  have horig : YangMillsFinite.CanForce A b :=
    (YangMillsFinite.presentation_invariant A b equiv).mp hforce
  exact (YangMillsFinite.dual_certificate A b y hb) horig

end

end YangMillsLongestChain

#print axioms YangMillsLongestChain.commutator_zero_implies_memory_zero
#print axioms YangMillsLongestChain.commutator_zero_implies_schur_reduces
#print axioms YangMillsLongestChain.transport_metric_memory_chain
#print axioms YangMillsLongestChain.resolved_penalty_preserves_retained_floor
#print axioms YangMillsLongestChain.resolved_schur_chain_to_full_floor
#print axioms YangMillsLongestChain.allocation_overlap_tail_chain
#print axioms YangMillsLongestChain.dual_certificate_survives_presentation
