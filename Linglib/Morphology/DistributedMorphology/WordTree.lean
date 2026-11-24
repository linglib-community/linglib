/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# The word tree of a complex head

The word tree of a complex head attaches each head on the side its exponent takes, innermost
first. On each side, its surface order outward from the root is then the order in which the heads
were merged.

## TODO

* Move `toTree` and `surface_eq` here from `Morphology/DistributedMorphology/Basic.lean`.
* A complex head is one root with a chain of heads, so a compound and a head with no root cannot
  be stated, and the order of the tree holds by the definition of `toTree`. Decide whether the
  shared type should be the more general `MorphosyntacticWord`.

## References

* [halle-marantz-1993]
* [baker-1985]
-/
