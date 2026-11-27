module

public import Linglib.Logic.Modal.Basic
public import Mathlib.Data.PFun

/-!
# Content modality

Some things have intentional content: books, rumours, beliefs, speech events. A content function
`con : α →. Set W` is a partial function that gives the set of worlds compatible with the content
of such a thing, and is undefined at a thing without content. We define the accessibility
relation `compatible con` between a thing and the worlds compatible with its content. A modal
whose domain is projected in this way is necessity or possibility along the relation, universal
and existential over the content (`box_compatible_iff`, `diamond_compatible_iff`), and so is a
*that*-clause that holds of the things whose content entails its proposition.

Necessity along the relation holds vacuously of a thing without content: the things at which `q`
is necessary are `con.core (Set.Iic {w | q w})` (`box_compatible_iff_mem_core`), and those among
them that have content are `con.preimage (Set.Iic {w | q w})` (`mem_preimage_Iic_iff`).

## Implementation notes

The content function is a `PFun`, as partial roles and partial denotations are, since a theorem
may turn on where it is defined. A clause that holds of the things whose content *is* its
proposition is not a modal along the relation: it is `p ∈ con x`, the preimage of `{p}`.

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

variable {α W : Type*} {con : α →. Set W} {a : α} {C : Set W} {w : W} {q : W → Prop}

/-- The accessibility relation of a content function relates a thing to the worlds compatible
with its content, and a thing without content to no world. -/
def compatible (con : α →. Set W) : SetRel α W :=
  {(a, w) | ∃ C ∈ con a, w ∈ C}

@[simp]
theorem mem_compatible : a ~[compatible con] w ↔ ∃ C ∈ con a, w ∈ C := .rfl

theorem mem_compatible_of_mem (h : C ∈ con a) : a ~[compatible con] w ↔ w ∈ C :=
  ⟨fun ⟨_, hC, hw⟩ ↦ Part.mem_unique hC h ▸ hw, fun hw ↦ ⟨C, h, hw⟩⟩

theorem box_compatible_iff (h : C ∈ con a) : □[compatible con] q a ↔ ∀ w ∈ C, q w :=
  forall_congr' fun _ ↦ imp_congr_left (mem_compatible_of_mem h)

theorem diamond_compatible_iff (h : C ∈ con a) : ◇[compatible con] q a ↔ ∃ w ∈ C, q w :=
  exists_congr fun _ ↦ and_congr_left' (mem_compatible_of_mem h)

theorem not_diamond_compatible (h : a ∉ con.Dom) : ¬ ◇[compatible con] q a :=
  fun ⟨_, ⟨C, hC, _⟩, _⟩ ↦ h (Part.dom_iff_mem.2 ⟨C, hC⟩)

/-- The content of a thing is necessary along the relation. -/
theorem box_compatible_of_mem (h : C ∈ con a) : □[compatible con] (· ∈ C) a :=
  (box_compatible_iff h).2 fun _ hw ↦ hw

/-- Consistent content is possible along the relation. -/
theorem diamond_compatible_of_mem (h : C ∈ con a) (hC : C.Nonempty) :
    ◇[compatible con] (· ∈ C) a :=
  (diamond_compatible_iff h).2 (hC.imp fun _ hw ↦ ⟨hw, hw⟩)

/-- A proposition is necessary along the relation at the things all of whose content entails
it, those without content among them. -/
theorem box_compatible_iff_mem_core : □[compatible con] q a ↔ a ∈ con.core (Set.Iic {w | q w}) :=
  ⟨fun h ↦ (PFun.mem_core ..).2 fun C hC ↦ Set.mem_Iic.2 fun v hw ↦ h v ⟨C, hC, hw⟩,
    fun h _ ⟨C, hC, hw⟩ ↦ (Set.mem_Iic.1 ((PFun.mem_core ..).1 h C hC) : C ⊆ _) hw⟩

/-- The things with content that entails a proposition are those with content at which the
proposition is necessary along the relation. -/
theorem mem_preimage_Iic_iff :
    a ∈ con.preimage (Set.Iic {w | q w}) ↔ a ∈ con.Dom ∧ □[compatible con] q a := by
  rw [PFun.preimage_eq, Set.mem_inter_iff, box_compatible_iff_mem_core, and_comm]

end Modality
