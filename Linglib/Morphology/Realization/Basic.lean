/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Realizations: indices realized in context

A realization assigns to an index and a context the finite set of forms that realize the index
there. Each index has a relation between contexts and forms, and an index is defective where the
relation is not total, overabundant where it is not single-valued, and syncretic where it is not
injective. Its exponents are its forms across its contexts, and it is suppletive when it has at
least two.

## TODO

* Move the structure, the relation of an index, exponents and suppletion, the cells of a form, the
  decidability instances and the order here from `Morphology/Realization.lean`.
* `Realization.Interpreted`, `IsIntrinsic`, `IsAllosemous` and `IsCrossCategorial` are stated in
  one framework's vocabulary and have one consuming study; move them to that framework or the
  study.

## References

* [corbett-2007]
* [stump-2016]
-/
