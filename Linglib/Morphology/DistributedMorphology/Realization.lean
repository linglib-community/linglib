/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Vocabulary Insertion as a realization

The realization by a list of Vocabulary Items inserts at each index and context the exponent the
Subset Principle selects in the neighborhood of that context.

## TODO

* Move `toRealization` and its lemmas here from
  `Morphology/DistributedMorphology/VocabularyInsertion/Basic.lean`.
* A Vocabulary Item has the fields of a `SubsetRule` whose features are positioned; state the map
  between them, so that insertion is the realization of a rule set
  (`Morphology/Exponence/Realization.lean`).

## References

* [halle-marantz-1993]
* [halle-1997]
-/
