# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The modules are finite: real symmetric block Hamiltonians, finite projectors, and explicit
  transport derivative hypotheses. No matrix exponential, continuum limit, or infinite-
  dimensional feedback is formalized.
* No physical dictionary is formalized: nothing here identifies the blocks with electrons,
  light, a spacetime metric, or a measured electrical response. The paper's measurement
  protocol and its data analysis are outside these proofs.
* `UPGProjectorDynamics` takes the endpoint derivatives of the transport as hypotheses; it does
  not construct the transport.

Formalization is evidence for the mathematics, not for the physical interpretation.
