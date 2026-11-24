/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# The realization of a rule set

A set of rules of exponence, with a way of choosing among the rules that apply, selects at most
one exponent in each context, and so realizes each index in each context by at most one form.

## TODO

* State the realization of a rule set for every type of rule, as `Realization.ofOption` of the
  selection. `Morphology/DistributedMorphology/VocabularyInsertion/Basic.lean` defines it for
  Vocabulary Items alone (`toRealization`), and neither `Morphology/Exponence/` nor
  `Morphology/Realization.lean` imports the other.
* Derive the properties every such realization has: it is single-valued, and it is defective where
  no rule applies.

## References

* [kiparsky-1973]
* [stump-2001]
-/
