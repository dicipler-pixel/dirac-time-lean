/-
Structural memory filtration (§3.1 of "The Dirac Time of the Gigantefermion",
Jeromie Beasley, DOI 10.5281/zenodo.22978631).

Successive reductions `R₀ → R₁ → ⋯ → R_m` define nested equivalence relations. A coarser
description cannot create a distinction the finer one did not possess: whatever the finer
record identifies, every later reduction still identifies.
-/
import Mathlib

namespace DiracTime.MemoryFiltration

/-- A coarser description cannot separate what the finer one identifies. -/
theorem coarser_cannot_separate {X Y Z : Type*} (R : X → Y) (g : Y → Z) {x y : X}
    (h : R x = R y) : g (R x) = g (R y) :=
  congrArg g h

/-- In linear form the kernels are nested: `ker R ≤ ker (g ∘ R)`. -/
theorem ker_le_ker_comp {K V W U : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    (R : V →ₗ[K] W) (g : W →ₗ[K] U) : LinearMap.ker R ≤ LinearMap.ker (g ∘ₗ R) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [LinearMap.comp_apply, hv, map_zero]

end DiracTime.MemoryFiltration
