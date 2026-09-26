# Provenance

| File | Source | Paper |
| :--- | :--- | :--- |
| `DiracTime/PredictiveQuotient.lean` | Written for this repository from §2 (2.1–2.4) of the paper | v3.0.1, DOI 10.5281/zenodo.22978631 |
| `DiracTime/Headline.lean` | Plain-Mathlib restatements, each proved by citing the library | same |
| `FalseControls/*.lean` | Written for this repository: small shift examples that each claim must reject | same |

Toolchain: Lean `v4.34.1`, Mathlib `v4.34.1` (the version Physlib uses, so later modules can
import Physlib's quantum-information library without a version change).

The SHA-256 of every checked source is written to `verification/report.json` on each run and
kept with the run's evidence.
