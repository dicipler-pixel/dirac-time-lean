# Provenance

| File | Source | Paper |
| :--- | :--- | :--- |
| `DiracTime/PredictiveQuotient.lean` | Written for this repository from §2 (2.1–2.4) of the paper | v3.0.1, DOI 10.5281/zenodo.22978631 |
| `DiracTime/MemoryFiltration.lean` | Written for this repository from §3.1 | same |
| `DiracTime/ProjectorTangent.lean` | Written for this repository from Theorem P1 (Appendix D) | same |
| `DiracTime/WeakValue.lean` | Written for this repository from Theorem P2 | same |
| `DiracTime/PathLedger.lean` | Written for this repository from Theorem P3 (§D.3) | same |
| `DiracTime/FiniteReturn.lean` | Written for this repository from Theorem P5, using `PredictiveQuotient` | same |
| `DiracTime/EntropyLedger.lean` | Written for this repository from Theorem P6 and Corollary P6.1 (§D.6) | same |
| `DiracTime/PhaseSilence.lean` | Written for this repository from §9.2 and Theorem 13.1 | same |
| `DiracTime/MovingFrame.lean` | Written for this repository from §9.3 and programme item T4 | same |
| `DiracTime/ProjectorBlocks.lean` | Written for this repository from Theorem P1, item 2 | same |
| `DiracTime/CommonClock.lean` | Written for this repository from Corollaries P4.1–P4.3 | same |
| `DiracTime/EqualEndpointWitness.lean` | Written for this repository from §11.4 | same |
| `DiracTime/FrictionMetric.lean` | Written for this repository from §12.6 | same |
| `DiracTime/SectorReduction.lean` | Written for this repository from §15.5 | same |
| `DiracTime/Headline.lean` | Plain-Mathlib restatements, each proved by citing the library | same |
| `FalseControls/*.lean` | Written for this repository: one small concrete counterexample per result, each of which must be rejected | same |

Toolchain: Lean `v4.34.1`, Mathlib `v4.34.1` (the version Physlib uses, so later modules can
import Physlib's quantum-information library without a version change).

The SHA-256 of every checked source is written to `verification/report.json` on each run and
kept with the run's evidence.
