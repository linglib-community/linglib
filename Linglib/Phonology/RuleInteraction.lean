module

public import Mathlib.Order.OrderDual

/-!
# Feeding and bleeding

This file defines feeding and bleeding, Kiparsky's relations between two rules: applying the
first to a form feeds the second when the second applies further to the result than to the form,
and bleeds it when the second applies less far. How far a rule applies takes values in any
preorder. A predicate, with `False < True`, gives Kiparsky's relations, [the first rule creating or
destroying a form the second applies to](##RuleInteraction.feeds_iff); the number of times the
second rule applies gives Baković and Blumenfeld's input-provision and input-removal. [In the
bleeding order the bled rule applies vacuously](##RuleInteraction.Bleeds.isFixedPt), as [the fed
rule does in the counterfeeding order](##RuleInteraction.Feeds.isFixedPt).

## Implementation notes

The relations take the first rule's map and the second rule's measure, not the rules themselves:
Kiparsky observes that they turn on what the rules do rather than on their form, and the two rules
may belong to different modules, as when impoverishment feeds metathesis.

## TODO

* Baković and Blumenfeld's input-rank, the `ℕ`-valued measure, and their output interactions.

## References

* [kiparsky-1968]
* [bakovic-blumenfeld-2024]
-/

@[expose] public section

namespace RuleInteraction

open Function OrderDual

variable {S α : Type*} [Preorder α]

/-- Applying `f` to `x` **feeds** the measure `r` when `r` is greater at `f x` than at `x`. With `r`
how far a second rule applies, the second rule applies further once `f` has applied: with a
predicate, it applies to `f x` but not to `x` (`feeds_iff`); with the number of times it applies,
`f` may also give a second locus to a rule that already applies to `x`. -/
def Feeds (f : S → S) (r : S → α) (x : S) : Prop := r x < r (f x)

/-- Applying `f` to `x` **bleeds** the measure `r` when `r` is smaller at `f x` than at `x`: with
a predicate, the second rule applies to `x` but not to `f x` (`bleeds_iff`). -/
def Bleeds (f : S → S) (r : S → α) (x : S) : Prop := r (f x) < r x

variable {f g : S → S} {r : S → α} {p : S → Prop} {x : S}

instance [DecidableLT α] : Decidable (Feeds f r x) := inferInstanceAs (Decidable (_ < _))

instance [DecidableLT α] : Decidable (Bleeds f r x) := inferInstanceAs (Decidable (_ < _))

theorem feeds_toDual_comp_iff : Feeds f (toDual ∘ r) x ↔ Bleeds f r x := Iff.rfl

theorem bleeds_toDual_comp_iff : Bleeds f (toDual ∘ r) x ↔ Feeds f r x := Iff.rfl

/-! ### Predicates -/

@[simp]
theorem feeds_iff : Feeds f p x ↔ ¬ p x ∧ p (f x) :=
  lt_iff_le_not_ge.trans
    ⟨fun h ↦ (not_imp.mp h.2).symm, fun h ↦ ⟨fun _ ↦ h.2, fun k ↦ h.1 (k h.2)⟩⟩

@[simp]
theorem bleeds_iff : Bleeds f p x ↔ p x ∧ ¬ p (f x) :=
  lt_iff_le_not_ge.trans ⟨fun h ↦ not_imp.mp h.2, fun h ↦ ⟨fun _ ↦ h.1, fun k ↦ h.2 (k h.1)⟩⟩

instance [DecidablePred p] : Decidable (Feeds f p x) := decidable_of_iff' _ feeds_iff

instance [DecidablePred p] : Decidable (Bleeds f p x) := decidable_of_iff' _ bleeds_iff

/-- In the bleeding order the bled rule applies vacuously: a map that changes only forms
satisfying `p` fixes the result of a map that bled `p`. -/
theorem Bleeds.isFixedPt (h : Bleeds f p x) (hg : ∀ y, ¬ p y → IsFixedPt g y) :
    IsFixedPt g (f x) :=
  hg _ (bleeds_iff.mp h).2

/-- In the counterfeeding order the fed rule applies vacuously: a map that changes only forms
satisfying `p` fixes a form at which `p` is fed. -/
theorem Feeds.isFixedPt (h : Feeds f p x) (hg : ∀ y, ¬ p y → IsFixedPt g y) : IsFixedPt g x :=
  hg _ (feeds_iff.mp h).1

end RuleInteraction
