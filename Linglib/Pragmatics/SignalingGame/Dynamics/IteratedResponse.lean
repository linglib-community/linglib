module

public import Linglib.Pragmatics.SignalingGame.BestResponse

/-!
# Iterated response

A sequence of sender and receiver types, each the response of one player to the last type of the
other, starting from the literal use of the signals. This file is to hold what the iterated best
response of [franke-2011] and the iterated cautious response of [jaeger-2014] share, which their
studies now define separately.

## TODO

* The response operators of the two studies as best responses of `SignalingGame.sender` and
  `SignalingGame.receiver`.
* A sequence along which the value does not fall is eventually periodic on a finite type of
  strategies, and its limit types are equilibria.
* The soft counterpart is the recursion of the Rational Speech Act model, whose speaker and
  listener are policies of the same agents at a finite rationality.

## References

* [franke-2011]
* [jaeger-2014]
-/
