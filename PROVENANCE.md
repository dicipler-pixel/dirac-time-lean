# Provenance

Every Lean file is a byte-identical copy of a verified source in the private
`operator-first` repository.

| Files | Source | Verified at |
| :--- | :--- | :--- |
| `ElementalFoundations`, `ElementalForceRecovery`, `ElementalBoundaryLedger`, `FalseControls/FalseControl.lean` | Revision 4, `research/elemental_foundations/formal/` (PR #25) | commit `6955e481b15b` (Actions run 34691594067, SUCCESS); identical on branch `research/elemental-foundations-v4` at `7e9f1ddc85d3` |
| `PauliMemory`, `FalseControls/FalseMemory.lean`, `FalseControls/FalsePauli.lean` | `research/combined_peel_hypersurface/formal/lean_4_33_0/` | branch `research/combined-peel-hypersurface-20260908` at `0afcc21e1a15` |

`ElementalFoundations` preserves the 16 theorems of the original PR #17 layer (commit
`8abd8cc23f22`, Actions run 34191153154) and adds 14. The SHA-256 of every checked file is
written to `verification/report.json` on each run.
