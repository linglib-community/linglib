module

public import Mathlib.Order.Basic
public import Mathlib.Data.Set.Basic

/-!
# Rules of exponence

A rule of exponence, in Matthews's sense, pairs an exponent with a condition on the contexts it
applies in. This file defines the interface for types of such rules, rule sets, and the set of
contexts a rule applies in, the key of Kiparsky's Elsewhere Condition, under which a rule is more
specific when it applies in fewer contexts.

## Main definitions

* `ExponenceRule`: a type of rules, each with an exponent and an applicability condition.
* `RuleSet`: a list of rules.
* `applySet`: the contexts a rule applies in.

## References

* [matthews-1991]
* [kiparsky-1973]
-/

@[expose] public section

namespace Morphology

/-- `ExponenceRule R Ctx E` says that `R` is a type of rules of exponence, each carrying an
exponent in `E` and applying in a class of contexts in `Ctx`. -/
class ExponenceRule (R : Type*) (Ctx E : outParam Type*) where
  /-- The exponent a rule inserts. -/
  exponent : R → E
  /-- The condition on contexts under which a rule applies. -/
  Applies : R → Ctx → Prop

export ExponenceRule (exponent Applies)

/-- A rule set is a list of rules of exponence. Selection by a key reads the list only to break
ties in the key, which no analysis should rest on: one that needs a tie decided states the order in
its key. A mechanism that is itself a scan of the list, such as strict scansion, reads the order. -/
abbrev RuleSet (R : Type*) := List R

variable {Ctx E : Type*} {R : Type*} [ExponenceRule R Ctx E]

/-- The contexts in which a rule applies. -/
def applySet (r : R) : Set Ctx := {c | Applies r c}

@[simp] theorem mem_applySet {r : R} {c : Ctx} :
    c ∈ applySet r ↔ Applies r c :=
  Iff.rfl

end Morphology
