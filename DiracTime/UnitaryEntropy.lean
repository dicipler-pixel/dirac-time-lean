/-
Unitary invariance of von Neumann entropy, and Theorem P6 with its unitarity hypothesis
discharged ("The Dirac Time of the Gigantefermion", Jeromie Beasley,
DOI 10.5281/zenodo.22978630).

Theorem P6 uses the fact that unitary evolution does not change the total entropy. Physlib's
quantum-information library defines the von Neumann entropy `Sᵥₙ` of a mixed state but does
not yet prove this invariance for a general unitary (it has it for SWAP and relabellings). It
is proved here from Physlib's own lemmas: the logarithm commutes with unitary conjugation,
and the Hilbert–Schmidt inner product is unitarily invariant.
-/
import QuantumInfo.Entropy.VonNeumann
import DiracTime.EntropyLedger

namespace DiracTime.UnitaryEntropy

open scoped InnerProductSpace RealInnerProductSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The state `U ρ U†`. -/
noncomputable def unitaryConj (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) : MState d where
  M := ρ.M.conj U.val
  nonneg := HermitianMat.conj_nonneg U.val ρ.nonneg
  tr := by rw [HermitianMat.trace_conj_unitary]; exact ρ.tr

/-- **Unitary invariance of von Neumann entropy**: `S(U ρ U†) = S(ρ)`. -/
theorem Sᵥₙ_unitaryConj (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    Sᵥₙ (unitaryConj ρ U) = Sᵥₙ ρ := by
  rw [Sᵥₙ_eq_neg_trace_log, Sᵥₙ_eq_neg_trace_log]
  show -⟪(ρ.M.conj U.val).log, ρ.M.conj U.val⟫ = -⟪ρ.M.log, ρ.M⟫
  rw [HermitianMat.log_conj_unitary, HermitianMat.inner_conj_unitary]

/-- **Total entropy is conserved under a unitary step**: `S(U ρ U†) − S(ρ) = 0`. This is the
unitarity hypothesis of `EntropyLedger`, discharged in the next theorem. -/
theorem total_entropy_conserved (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    Sᵥₙ (unitaryConj ρ U) - Sᵥₙ ρ = 0 := by
  rw [Sᵥₙ_unitaryConj, sub_self]

/-- **Theorem P6 with the unitarity hypothesis discharged.** The total state evolves as
`ρ ↦ U ρ U†` and its entropy is Physlib's `Sᵥₙ`; the identity then needs only the Gibbs-reference
form of the relative entropies. The system and reservoir entropies, energies and relative
entropies remain real parameters. -/
theorem entropy_correlation_identity_unitary {ι : Type*} (s : Finset ι) (β logZ : ι → ℝ)
    (SS₀ SS₁ : ℝ) (Sr₀ Sr₁ Er₀ Er₁ Dr₀ Dr₁ : ι → ℝ) (ρ : MState d)
    (U : Matrix.unitaryGroup d ℂ)
    (hD₀ : ∀ r ∈ s, Dr₀ r = -Sr₀ r + β r * Er₀ r + logZ r)
    (hD₁ : ∀ r ∈ s, Dr₁ r = -Sr₁ r + β r * Er₁ r + logZ r) :
    let I₀ := SS₀ + ∑ r ∈ s, Sr₀ r - Sᵥₙ ρ
    let I₁ := SS₁ + ∑ r ∈ s, Sr₁ r - Sᵥₙ (unitaryConj ρ U)
    let Q := fun r => -(Er₁ r - Er₀ r)
    (SS₁ - SS₀) - ∑ r ∈ s, β r * Q r = (I₁ - I₀) + ∑ r ∈ s, (Dr₁ r - Dr₀ r) :=
  DiracTime.EntropyLedger.entropy_correlation_identity s β logZ SS₀ SS₁ (Sᵥₙ ρ)
    (Sᵥₙ (unitaryConj ρ U)) Sr₀ Sr₁ Er₀ Er₁ Dr₀ Dr₁ hD₀ hD₁ (Sᵥₙ_unitaryConj ρ U)

end DiracTime.UnitaryEntropy
