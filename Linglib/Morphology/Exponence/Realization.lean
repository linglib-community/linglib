/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Exponence.Select
public import Linglib.Morphology.Realization.Basic

/-!
# The realization of a rule set

A set of rules of exponence, with a ranking `f` that chooses among the rules that apply, selects
at most one exponent in each context. Given the site `site i c` at which an index `i` is realized
in a context `c`, it therefore realizes each index in each context by at most one form:
`v.toRealization f site` is `Realization.ofOption` of the selection. This is the map from rule
sets into realizations, of which Vocabulary Insertion by the Subset Principle is the case of
Vocabulary Items ranked by their specificity.

## Main definitions

* `RuleSet.toRealization`: the realization of a rule set.

## Main results

* `RuleSet.isUnivalent_toRealization`: the realization of a rule set has at most one form in a
  cell.
* `RuleSet.isLicensed_toRealization_iff`: an index is licensed in a context exactly when some rule
  applies at its site.
* `RuleSet.isSuppletive_toRealization_iff`: an index is suppletive exactly when two of its
  contexts select distinct exponents.

## TODO

* The realization of a rule set under selection by a specificity key, `RuleSet.realizeMinimal`.
* The realizations of the other rule types, `SubsetRule`, `SupersetRule`, `SpanRule` and the
  rules of a paradigm function, as cases of this one.

## References

* [kiparsky-1973]
* [stump-2001]
-/

@[expose] public section

namespace Morphology.RuleSet

variable {Ctx E R : Type*} [ExponenceRule R Ctx E] [DecidableRel (Applies : R → Ctx → Prop)]
  {α : Type*} [LinearOrder α] {I C : Type*}
  {v : RuleSet R} {f : R → α} {site : I → C → Ctx} {i : I} {c : C}

/-- The realization of a rule set: at each index and context, the exponent of the rule that `f`
ranks first among those applying at the site of the index in the context. -/
def toRealization (v : RuleSet R) (f : R → α) (site : I → C → Ctx) : Realization I C E :=
  .ofOption fun i c ↦ v.realize f (site i c)

@[simp] theorem toRealization_realize (i : I) (c : C) :
    (v.toRealization f site).realize i c = (v.realize f (site i c)).toFinset := rfl

/-- Selection picks one rule, so the realization of a rule set has at most one form in a cell. -/
theorem isUnivalent_toRealization : (v.toRealization f site).IsUnivalent :=
  Realization.isUnivalent_ofOption _

/-- An index is licensed in a context exactly when some rule applies at its site. -/
theorem isLicensed_toRealization_iff :
    (v.toRealization f site).IsLicensed i c ↔ ∃ r ∈ v, Applies r (site i c) := by
  rw [toRealization, Realization.isLicensed_ofOption_iff, realize, Option.isSome_map,
    selectBy_isSome_iff]

/-- An index is suppletive exactly when two of its contexts select distinct exponents. -/
theorem isSuppletive_toRealization_iff : (v.toRealization f site).IsSuppletive i ↔
    ∃ c c' e e', v.realize f (site i c) = some e ∧ v.realize f (site i c') = some e' ∧ e ≠ e' :=
  Realization.isSuppletive_ofOption_iff

end Morphology.RuleSet
