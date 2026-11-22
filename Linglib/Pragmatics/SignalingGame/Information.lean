module

public import Linglib.Core.Probability.Decision.Blackwell
public import Linglib.Pragmatics.SignalingGame.Defs

/-!
# The sender as an experiment

A sender is a statistical experiment on the state, and a receiver decides on its outcome. This
file is to relate the values of a signaling game to the comparison of experiments in
`Linglib.Core.Probability.Decision.Blackwell` and to the value of information.

## TODO

* The receiver's best value against a garbling of a sender is no more than against the sender.
* The bound on a sender whose signal does not depend on the state, `success_const_le`, as the
  case of the uninformative experiment.
* The receiver's best value against a sender as a `decisionValue` of the posterior, and its
  excess over the value of the prior as a `valueOfInformation`.

## References

* [blackwell-1953]
-/
