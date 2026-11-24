/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.Basic
public import Linglib.Morphology.Exponence.Realization

/-!
# Vocabulary Insertion as a realization

The realization by a list of Vocabulary Items inserts at each index and context the exponent the
Subset Principle selects in the neighborhood of that context. It is the realization of the items
as a rule set ranked by their specificity, `RuleSet.toRealization`, so it has at most one form in
each cell.

## Main definitions

* `DistributedMorphology.toRealization`: the realization by a list of Vocabulary Items.

## Main results

* `DistributedMorphology.toRealization_isUnivalent`: Vocabulary Insertion realizes no cell
  overabundantly.
* `DistributedMorphology.toRealization_isSuppletive_iff`: an index is suppletive exactly when two
  of its contexts select items with distinct exponents.

## TODO

* A Vocabulary Item has the fields of a `SubsetRule` whose features are positioned; state the map
  between them.

## References

* [halle-marantz-1993]
* [halle-1997]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology

section Realization

variable {F E R Ctx : Type*} [DecidableEq F] {items : RuleSet (VocabularyItem F E)}
  {site : R → Ctx → Neighborhood (Finset F)} {r : R}

/-- The realization by `items` inserts at each index and context the exponent the Subset Principle
selects in the neighborhood `site r c`. -/
def toRealization (items : RuleSet (VocabularyItem F E))
    (site : R → Ctx → Neighborhood (Finset F)) : Morphology.Realization R Ctx E :=
  items.toRealization VocabularyItem.specificity site

@[simp] theorem toRealization_realize (r : R) (c : Ctx) :
    (toRealization items site).realize r c = (subsetPrinciple items (site r c)).toFinset := rfl

/-- The Subset Principle selects one item, so Vocabulary Insertion realizes no cell
overabundantly. -/
theorem toRealization_isUnivalent : (toRealization items site).IsUnivalent :=
  RuleSet.isUnivalent_toRealization

/-- An index is suppletive exactly when two of its contexts select items with distinct
exponents. -/
theorem toRealization_isSuppletive_iff : (toRealization items site).IsSuppletive r ↔
    ∃ c c' e e', subsetPrinciple items (site r c) = some e ∧
      subsetPrinciple items (site r c') = some e' ∧ e ≠ e' :=
  RuleSet.isSuppletive_toRealization_iff

end Realization

end DistributedMorphology
