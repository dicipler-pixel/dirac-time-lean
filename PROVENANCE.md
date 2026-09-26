# Provenance

Every Lean file is a byte-identical copy of a verified source in the private
`operator-first` repository.

| File | Source | Verified at |
| :--- | :--- | :--- |
| `Gravity.lean` | PR #8, "Gravity: verified projector algebra and exact moving-wall example" | commit `2ded71b0e7a7` (Actions run 34035655097); unchanged at PR #9 |
| `GravityOverlap.lean` | PR #9, "Finite projector overlap: close the Taylor bridge under C1 assumptions" | commit `63c11a656ea7` (Actions run 34130027417) |
| `FalseControls/*.lean` | the four controls in PR #8's `scripts/verify_gravity.py`, written out as files | same |

`Gravity.lean` is also the file shipped, with the same SHA-256, in the Edition 6 package
`Gravity_Ledger_Edition_6_Complete_Paper_and_Proofs_20260924` (`lean/Gravity.lean`). The
SHA-256 of every checked file is written to `verification/report.json` on each run.
