# Provenance

Every Lean file is a byte-identical copy of a source in the private `operator-first`
repository, taken from branch `formal/yang-mills-longest-chain-2026-09-13` at commit
`3eb82d5f5dd5`, which carries the union of the Yang–Mills lanes.

| Files | Source directory | Earlier verification |
| :--- | :--- | :--- |
| `GaugeCertificates.lean`, `FalseControls/GaugeControl.lean` | `research/yang_mills_2026_09_09/lean/` | PR #18, commit `4c90eaa499cd` |
| `CrossTheorem`, `MatrixResolvedBoundary`, `FalseControls/CrossTheoremControl.lean` | `research/yang_mills_2026_09_09/cross_theorem/lean/` | PR #18; PR #27 (Actions run 34698115560) |
| `SchurCongruence`, `ProjectorKernel`, `CouplingFeedback`, `ObservabilityKernel`, `ProjectorDynamics` | same | PR #51 |
| `TailGapTransfer`, `SchurFloorTransfer`, `NonuniformAllocationFloor` | same | PRs #52, #54, #56 |
| `LongestYangMillsChain` | same | this branch |

Several of the later lanes were recorded as audited drafts before their CI closed; the check in
this repository is the verification of the complete set. The SHA-256 of every checked file is
written to `verification/report.json` on each run.
