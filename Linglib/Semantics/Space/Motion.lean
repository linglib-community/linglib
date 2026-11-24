module

/-!
# The path of an event

An event of motion has a path: the sequence of places its moving participant passes through. A
directional locative describes this path, so *walk to the house* holds of the walking events whose
path leads to the house.

This file is the home of the map from events to their paths. The map is a homomorphism: the path
of two events put together is the two paths put together.

## TODO

* The type of the map. The part structure of events is a join in some sources and a partial
  concatenation in others.
* The denotation of a verb with a directional locative is `V ∩ σ ⁻¹' X`, for a set `V` of events,
  a set `X` of paths and the map `σ`. State how properties of `X` pass to it.

## References

* [zwarts-2005]
* [krifka-1998]
-/
