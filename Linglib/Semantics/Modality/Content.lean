module

public import Linglib.Logic.Modal.Defs

/-!
# Content modality

Some things have intentional content: books, rumours, beliefs, speech events. A content function
`con : α → Option (Set W)` gives the set of worlds compatible with the content of such a thing,
and is undefined at a thing without content. We define the accessibility relation
`compatible con` between a thing and the worlds compatible with its content. A modal whose domain
is projected in this way is necessity or possibility along the relation, universal and
existential over the content (`box_compatible_iff`, `diamond_compatible_iff`), and so is a
*that*-clause that holds of the things whose content entails its proposition.

## Implementation notes

A thing without content is related to no world, so possibility over it is false and necessity
vacuously true. A clause that holds of the things whose content *is* its proposition is not a
modal along the relation: it is `p ∈ con x`.

## References

* [kratzer-2006]
* [hacquard-2006]
* [hacquard-2010]
* [kratzer-2013]
-/

@[expose] public section

namespace Modality

open ModalLogic
open scoped SetRel

variable {α W : Type*} {con : α → Option (Set W)} {a : α} {C : Set W} {w : W} {q : W → Prop}

/-- The accessibility relation of a content function relates a thing to the worlds compatible
with its content, and a thing without content to no world. -/
def compatible (con : α → Option (Set W)) : SetRel α W :=
  .ofSuccessors fun a ↦ (con a).getD ∅

@[simp]
theorem mem_compatible : a ~[compatible con] w ↔ ∃ C ∈ con a, w ∈ C := by
  cases h : con a <;> simp [compatible, h]

theorem mem_compatible_of_eq_some (h : con a = some C) :
    a ~[compatible con] w ↔ w ∈ C := by
  simp [h]

theorem box_compatible_iff (h : con a = some C) :
    □[compatible con] q a ↔ ∀ w ∈ C, q w :=
  forall_congr' fun _ ↦ imp_congr_left (mem_compatible_of_eq_some h)

theorem diamond_compatible_iff (h : con a = some C) :
    ◇[compatible con] q a ↔ ∃ w ∈ C, q w :=
  exists_congr fun _ ↦ and_congr_left' (mem_compatible_of_eq_some h)

theorem not_diamond_compatible (h : con a = none) : ¬ ◇[compatible con] q a :=
  fun ⟨_, hw, _⟩ ↦ by simp [h] at hw

/-- The content of a thing is necessary along the relation. -/
theorem box_compatible_of_mem (h : C ∈ con a) : □[compatible con] (· ∈ C) a :=
  (box_compatible_iff h).2 fun _ hw ↦ hw

/-- Consistent content is possible along the relation. -/
theorem diamond_compatible_of_mem (h : C ∈ con a) (hC : C.Nonempty) :
    ◇[compatible con] (· ∈ C) a :=
  (diamond_compatible_iff h).2 (hC.imp fun _ hw ↦ ⟨hw, hw⟩)

end Modality
