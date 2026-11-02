module

public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.OrderDual

/-!
# Feeding and bleeding

This file defines Kiparsky's feeding and bleeding: applying one rule to a form feeds a second when
the second applies further to the result than to the form, and bleeds it when it applies less far,
how far being measured in any preorder. [A predicate, with `False < True`, gives Kiparsky's
relations](##RuleInteraction.feeds_iff), the number of times the second rule applies Baković and
Blumenfeld's input-provision and input-removal, and [a coarser measure fewer
interactions](##RuleInteraction.Feeds.of_comp). [In the bleeding order the bled rule applies
vacuously](##RuleInteraction.Bleeds.isFixedPt), and [a map undoing the first rule bleeds what it
feeds](##RuleInteraction.bleeds_iff_feeds_of_apply_eq).

## Implementation notes

The relations take the first rule's map and the second rule's measure, not the rules themselves:
Kiparsky observes that they turn on what the rules do rather than on their form, and the two rules
may belong to different modules, as when impoverishment feeds metathesis.

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

/-- A map undoing `f` at `x` bleeds at `f x` what `f` feeds at `x`: flipping a rule turns its
feeding into bleeding. -/
theorem bleeds_iff_feeds_of_apply_eq (h : g (f x) = x) : Bleeds g r (f x) ↔ Feeds f r x := by
  rw [Bleeds, h, Feeds]

/-- A measure read through a monotone map feeds only where the measure itself does: coarsening
how far a rule applies can lose interactions but not create them. -/
theorem Feeds.of_comp {β : Type*} [LinearOrder β] {φ : β → α} {s : S → β} (hφ : Monotone φ)
    (h : Feeds f (φ ∘ s) x) : Feeds f s x :=
  hφ.reflect_lt h

theorem Bleeds.of_comp {β : Type*} [LinearOrder β] {φ : β → α} {s : S → β} (hφ : Monotone φ)
    (h : Bleeds f (φ ∘ s) x) : Bleeds f s x :=
  hφ.reflect_lt h

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
