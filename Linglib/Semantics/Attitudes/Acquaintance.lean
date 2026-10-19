module

public import Mathlib.Data.Set.Defs

/-!
# De re attitudes by acquaintance

For Lewis the objects of attitudes are properties of centers, a subject at a time in a world.
A subject ascribes a property to a res under a relation when she bears the relation uniquely to
the res and self-ascribes the property of bearing it uniquely to something with the property; a
de re belief is such an ascription under a relation of acquaintance. A concept, a value at each
center, is the relation each center bears to its value there, and identity, the concept of the
self, makes belief de se the case of belief de re through identity.

## Main definitions

* `Acquaintance.BearsUniquely`: a center bears a relation to a value and to nothing else.
* `Acquaintance.deRe`: the property of bearing a relation uniquely to something with a property.
* `Acquaintance.AscribesUnder`: ascription of a property to a res under a relation.
* `Acquaintance.ofConcept`: the relation of a concept.

## Main statements

* `Acquaintance.BearsUniquely.unique`: a center bears a relation uniquely to at most one value.
* `Acquaintance.mem_deRe_ofConcept`: through a concept, the de re property is the property of
  the concept's value.
* `Acquaintance.ascribesUnder_ofConcept`, `Acquaintance.ascribesUnder_ofConcept_apply`: ascription
  under a concept, and ascription under identity as self-ascription.

## References

* [lewis-1979-attitudes]
* [cresswell-vonstechow-1982]
* [heim-1994-comments]
* [abusch-1997]
-/

@[expose] public section

namespace Acquaintance

variable {α C : Type*} {R : α → C → Prop} {P : α → Set C} {A : Set C} {c : C → α} {p : C}
  {y y' : α}

/-- The center `p` bears `R` uniquely to `y` when `R y p` holds and `R z p` holds of no other
`z`. -/
def BearsUniquely (R : α → C → Prop) (p : C) (y : α) : Prop := ∀ z, R z p ↔ z = y

/-- The property of bearing `R` uniquely to something that has `P`, the centers that do. -/
def deRe (R : α → C → Prop) (P : α → Set C) : Set C := {p | ∃ y, BearsUniquely R p y ∧ p ∈ P y}

/-- At the center `p`, with attitude alternatives `A`, the subject ascribes `P` to `y` under `R`
when she bears `R` uniquely to `y` and self-ascribes the property of bearing `R` uniquely to
something that has `P`, every alternative having it. -/
def AscribesUnder (A : Set C) (p : C) (R : α → C → Prop) (y : α) (P : α → Set C) : Prop :=
  BearsUniquely R p y ∧ A ⊆ deRe R P

/-- The relation of a concept `c` relates each center to the value of `c` there. -/
def ofConcept (c : C → α) (y : α) (p : C) : Prop := y = c p

theorem BearsUniquely.rel (h : BearsUniquely R p y) : R y p := (h y).2 rfl

theorem BearsUniquely.eq (h : BearsUniquely R p y) {z : α} (hz : R z p) : z = y := (h z).1 hz

theorem BearsUniquely.unique (h : BearsUniquely R p y) (h' : BearsUniquely R p y') : y = y' :=
  h'.eq h.rel

theorem BearsUniquely.mem_deRe_iff (h : BearsUniquely R p y) : p ∈ deRe R P ↔ p ∈ P y :=
  ⟨fun ⟨_, h', hP⟩ ↦ h'.unique h ▸ hP, fun hP ↦ ⟨y, h, hP⟩⟩

theorem bearsUniquely_ofConcept_iff : BearsUniquely (ofConcept c) p y ↔ y = c p :=
  ⟨fun h ↦ h.rel, fun h _ ↦ h ▸ Iff.rfl⟩

theorem bearsUniquely_ofConcept (c : C → α) (p : C) : BearsUniquely (ofConcept c) p (c p) :=
  bearsUniquely_ofConcept_iff.2 rfl

@[simp] theorem mem_deRe_ofConcept : p ∈ deRe (ofConcept c) P ↔ p ∈ P (c p) :=
  (bearsUniquely_ofConcept c p).mem_deRe_iff

theorem ascribesUnder_ofConcept :
    AscribesUnder A p (ofConcept c) y P ↔ y = c p ∧ ∀ q ∈ A, q ∈ P (c q) :=
  and_congr bearsUniquely_ofConcept_iff
    ⟨fun h _ hq ↦ mem_deRe_ofConcept.1 (h hq), fun h _ hq ↦ mem_deRe_ofConcept.2 (h _ hq)⟩

/-- Ascribing `P` under a concept to its value at the subject's own center is self-ascribing the
property of the concept's value. With the self of each center as the concept, identity, this is
Lewis's reduction of belief de se to belief de re. -/
theorem ascribesUnder_ofConcept_apply :
    AscribesUnder A p (ofConcept c) (c p) P ↔ ∀ q ∈ A, q ∈ P (c q) := by
  simp [ascribesUnder_ofConcept]

end Acquaintance
