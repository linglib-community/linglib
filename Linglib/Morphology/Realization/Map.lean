/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Maps of realizations

A realization is carried along a map of its forms, pulled back along maps of its indices and
contexts, composed with a realization of its forms, and reduced by the kernel of its assignment.

## TODO

* Move `Realization.map`, `comp`, `comap`, `reduce` and the transpose here from
  `Morphology/Realization.lean`, with the lemmas that a property is preserved or reflected by a
  map, such as `IsSyncretic.map` and `IsSuppletive.of_map`.
* The lemmas of `Morphology/Paradigm/Linkage.lean` about invariance along a projection are
  instances of these and belong here.

## References

* [corbett-2007]
* [stump-2016]
-/
