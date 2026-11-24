module

public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.OrderDual

/-!
# Feeding and bleeding

Two rules interact when applying one changes how far the other applies. Let `f : S → S` be the
first rule and `m : S → α` a measure, in a preorder, of how far the second applies to a form. We
say that `f` *feeds* `m` at `x` when `m x < m (f x)`, and *bleeds* it when `m (f x) < m x`.

When `m` is a predicate, the description of the second rule, feeding at `x` says that `f x`
meets the description and `x` does not: the application of the first rule creates a form to
which the second is applicable, and bleeding removes one. When `m` counts the places at which
the second rule applies, the relations are input-provision and input-removal.

The second rule is often a map `g`, and the measure is then whether `g` changes a form,
`¬ IsFixedPt g x`. In these terms `f` feeds nowhere exactly when it maps the fixed points of `g`
to fixed points of `g`, so commuting maps do not feed each other, and where `f` feeds, the two
orders of application give different results. In the order in which `g` applies first, the
counterfeeding order, `g` changes nothing, and `f` then gives a form that `g` would change; if
`f` has nothing to do once `g` has applied to that form, the result is not a fixed point of the
two rules applied in that order.

## Main definitions

* `Phonology.Feeds`, `Phonology.Bleeds`: a map raises, or lowers, a measure at a form.

## Main results

* `Phonology.feeds_iff`, `Phonology.bleeds_iff`: the relations for a predicate.
* `Phonology.Feeds.not_isFixedPt`, `Phonology.Bleeds.not_isFixedPt`: the first rule changes a
  form at which it feeds or bleeds.
* `Phonology.Feeds.of_comp`, `Phonology.Bleeds.of_comp`: a measure read through a monotone map
  has no interactions that the measure lacks.
* `Phonology.Bleeds.isFixedPt`, `Phonology.Feeds.isFixedPt`: a rule that changes only forms
  meeting its description applies vacuously after a rule that bled it, and before one that
  feeds it.
* `Phonology.forall_not_feeds_iff_mapsTo`: a map feeds the changes of another nowhere exactly
  when it preserves the other's fixed points.
* `Phonology.Feeds.apply_ne_apply`, `Function.Commute.not_feeds`: where one map feeds the
  changes of another the two orders of application differ, so commuting maps do not feed.
* `Phonology.Feeds.underapplication`, `Phonology.Feeds.not_isFixedPt_comp`: in the
  counterfeeding order the fed rule underapplies, and the result is not a fixed point of the
  composite.
* `Phonology.bleeds_iff_feeds_of_apply_eq`: a map undoing the first rule bleeds what it feeds.

## Implementation notes

The relations take the first rule's map and the second rule's measure, not two rules.
[kiparsky-1968] defines feeding and bleeding as functional relationships between rules, by what
the application of one does to the forms the other applies to. Stated of a map and a measure,
the relations also hold between rules of different modules, as when impoverishment feeds
metathesis. They hold at a form, as [bakovic-blumenfeld-2024] define them, and a relation
between rules is the existence of such a form.

A measure in a preorder covers both the set of forms a rule applies to and the number of places
at which it applies, the input-rank of [bakovic-blumenfeld-2024].

## References

* [P. Kiparsky, *Linguistic Universals and Linguistic Change* (1968)][kiparsky-1968]
* [E. Baković and L. Blumenfeld, *A formal typology of process interactions*
  (2024)][bakovic-blumenfeld-2024]
-/

@[expose] public section

namespace Phonology

open Function OrderDual

variable {S α : Type*} [Preorder α]

/-- Applying `f` to `x` feeds the measure `m` when `m` is greater at `f x` than at `x`. -/
def Feeds (f : S → S) (m : S → α) (x : S) : Prop := m x < m (f x)

/-- Applying `f` to `x` bleeds the measure `m` when `m` is smaller at `f x` than at `x`. -/
def Bleeds (f : S → S) (m : S → α) (x : S) : Prop := m (f x) < m x

variable {f g : S → S} {m : S → α} {p : S → Prop} {x : S}

instance [DecidableLT α] : Decidable (Feeds f m x) := inferInstanceAs (Decidable (_ < _))

instance [DecidableLT α] : Decidable (Bleeds f m x) := inferInstanceAs (Decidable (_ < _))

theorem feeds_toDual_comp_iff : Feeds f (toDual ∘ m) x ↔ Bleeds f m x := Iff.rfl

theorem bleeds_toDual_comp_iff : Bleeds f (toDual ∘ m) x ↔ Feeds f m x := Iff.rfl

/-- A rule changes a form at which it feeds. -/
theorem Feeds.not_isFixedPt (h : Feeds f m x) : ¬ IsFixedPt f x := fun hx ↦ by
  rw [Feeds, hx.eq] at h
  exact lt_irrefl _ h

/-- A rule changes a form at which it bleeds. -/
theorem Bleeds.not_isFixedPt (h : Bleeds f m x) : ¬ IsFixedPt f x := fun hx ↦ by
  rw [Bleeds, hx.eq] at h
  exact lt_irrefl _ h

/-- A rule does not both feed and bleed a measure at a form. -/
theorem Feeds.not_bleeds (h : Feeds f m x) : ¬ Bleeds f m x := lt_asymm h

/-- A map undoing `f` at `x` bleeds at `f x` what `f` feeds at `x`. -/
theorem bleeds_iff_feeds_of_apply_eq (h : g (f x) = x) : Bleeds g m (f x) ↔ Feeds f m x := by
  rw [Bleeds, h, Feeds]

/-- A measure read through a monotone map feeds only where the measure itself does: coarsening
how far a rule applies can lose interactions and cannot create them. -/
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

/-! ### Rules as maps

The measure of a rule `g` is here whether it changes a form. -/

/-- `f` feeds the changes of `g` at a form that `g` fixes and whose image `g` changes. -/
theorem feeds_not_isFixedPt_iff :
    Feeds f (¬ IsFixedPt g ·) x ↔ IsFixedPt g x ∧ ¬ IsFixedPt g (f x) := by
  rw [feeds_iff, not_not]

/-- `f` bleeds the changes of `g` at a form that `g` changes and whose image `g` fixes. -/
theorem bleeds_not_isFixedPt_iff :
    Bleeds f (¬ IsFixedPt g ·) x ↔ ¬ IsFixedPt g x ∧ IsFixedPt g (f x) := by
  rw [bleeds_iff, not_not]

/-- `f` feeds the changes of `g` nowhere exactly when it maps the fixed points of `g` to fixed
points of `g`. -/
theorem forall_not_feeds_iff_mapsTo :
    (∀ x, ¬ Feeds f (¬ IsFixedPt g ·) x) ↔ Set.MapsTo f (fixedPoints g) (fixedPoints g) := by
  simp only [feeds_not_isFixedPt_iff, not_and, not_not]
  rfl

/-- Where `f` feeds the changes of `g`, the two orders of application give different
results. -/
theorem Feeds.apply_ne_apply (h : Feeds f (¬ IsFixedPt g ·) x) : f (g x) ≠ g (f x) := by
  obtain ⟨hx, hfx⟩ := feeds_not_isFixedPt_iff.1 h
  rw [hx.eq]
  exact fun he ↦ hfx he.symm

/-- Where `f` bleeds the changes of `g`, the two orders of application agree exactly when `f`
gives the form and its image under `g` the same image. -/
theorem Bleeds.apply_eq_apply_iff (h : Bleeds f (¬ IsFixedPt g ·) x) :
    f (g x) = g (f x) ↔ f (g x) = f x := by
  rw [(bleeds_not_isFixedPt_iff.1 h).2.eq]

/-- Commuting maps do not feed each other's changes. -/
theorem _root_.Function.Commute.not_feeds (h : Function.Commute f g) :
    ¬ Feeds f (¬ IsFixedPt g ·) x := fun hf ↦ hf.apply_ne_apply (h.eq x)

/-- In the counterfeeding order the fed rule underapplies: where `f` makes a form that `g` changes,
applying `g` first gives what `f` alone gives, a form that `g` would change. -/
theorem Feeds.underapplication (h : Feeds f (¬ IsFixedPt g ·) x) :
    f (g x) = f x ∧ ¬ IsFixedPt g (f (g x)) := by
  obtain ⟨hx, hfx⟩ := feeds_not_isFixedPt_iff.1 h
  rw [hx.eq]
  exact ⟨rfl, hfx⟩

/-- The result of the counterfeeding order is not a fixed point of the two rules applied in that
order, when `f` changes nothing once `g` has applied to that result. -/
theorem Feeds.not_isFixedPt_comp (h : Feeds f (¬ IsFixedPt g ·) x)
    (hf : IsFixedPt f (g (f x))) : ¬ IsFixedPt (f ∘ g) ((f ∘ g) x) := fun he ↦ by
  obtain ⟨hx, hfx⟩ := feeds_not_isFixedPt_iff.1 h
  simp only [IsFixedPt, comp_apply, hx.eq] at he
  exact hfx (hf.symm.trans he)

end Phonology
