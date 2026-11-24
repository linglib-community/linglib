/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# The paradigm function as a paradigm linkage

Under the default rule of paradigm linkage, what a linkage realizes at a cell is the value of the
paradigm function there.

## TODO

* Move `Morphology.Linkage.realized_eq_paradigmFunction` here from
  `Morphology/Paradigm/Function.lean`. The structure `Linkage` extends `Realization` and has a
  consumer outside this framework, so it stays shared.

## References

* [stump-2006]
* [bonami-stump-2016]
-/
