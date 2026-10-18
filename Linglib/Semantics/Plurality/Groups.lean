module

public import Mathlib.Data.Finset.Grade
public import Mathlib.Logic.Equiv.Finset
public import Linglib.Semantics.Mereology

/-!
# Group formation

This file defines Landman's group operators on a join-semilattice `E` of individuals or events.
Formation `up` packs a plural sum into an atom, the group, and dissolution `down` recovers the
sum. The carrier is any `SemilatticeSup`, so the operators serve individuals and events alike;
Siloni uses the event version to dissolve a symmetric verb's atomic event into its directional
sub-events. A model on finite sets shows the two laws consistent.

## Definitions

* `Plurality.GroupStructure E`: `up` and `down`, with a group an atom and dissolution the
  inverse of formation.
* `Plurality.GroupStructure.finsetModel β`: the model on `Finset (β ⊕ ℕ)`, packing a plurality
  into the singleton of a fresh marker indexed by its code.

## Main results

* `Plurality.GroupStructure.up_injective`: distinct sums form distinct groups.

## Implementation notes

* Landman's set-theoretic model identifies group formation with singleton formation and defines
  dissolution only on groups, the singleton sets of sets. Here `down` is total, and the
  left-inverse law constrains it only on the image of `up`.
* The finite-set model follows the singleton construction, with a fresh marker standing for the
  plurality so that groups and ordinary atoms share one carrier.

## References

* [F. Landman, *Groups, I* (1989)][landman-1989]
* [F. Landman, *Events and plurality* (2000)][landman-2000]
* [T. Siloni, *Reciprocal verbs and symmetry* (2012)][siloni-2012]
-/

@[expose] public section

namespace Plurality

/-- Landman's group structure, in which `up` packs a sum into a group atom and `down` recovers
the sum. -/
structure GroupStructure (E : Type*) [SemilatticeSup E] where
  /-- Group formation. -/
  up : E → E
  /-- Group dissolution. -/
  down : E → E
  /-- A group is an atom. -/
  atom_up (x : E) : Mereology.Atom (up x)
  /-- Dissolution is a left inverse of formation. -/
  down_up : Function.LeftInverse down up

namespace GroupStructure

variable {E : Type*} [SemilatticeSup E] (G : GroupStructure E)

theorem up_injective : Function.Injective G.up := G.down_up.injective

/-! ### A model

Finite subsets of `β ⊕ ℕ` under union: the `β`-singletons are the ordinary atoms, and packing
recruits the singleton of a fresh `ℕ`-marker for each plurality, so groups are atoms of the same
domain. -/

variable {β : Type*} [Encodable β]

/-- Group formation in the model sends a plurality to the singleton of the marker indexed by
its code. -/
def modelUp (x : Finset (β ⊕ ℕ)) : Finset (β ⊕ ℕ) :=
  {Sum.inr (Encodable.encode x)}

theorem modelUp_injective : Function.Injective (modelUp (β := β)) := fun _ _ h ↦
  Encodable.encode_injective (Sum.inr.inj (Finset.singleton_injective h))

/-- The finite sets of `β ⊕ ℕ` carry a group structure, with dissolution the left inverse of
formation. -/
noncomputable def finsetModel (β : Type*) [DecidableEq β] [Encodable β] :
    GroupStructure (Finset (β ⊕ ℕ)) where
  up := modelUp
  down := Function.invFun modelUp
  atom_up _ := Mereology.atom_iff_isAtom.2 (Finset.isAtom_singleton _)
  down_up := Function.leftInverse_invFun modelUp_injective

@[simp] theorem finsetModel_up [DecidableEq β] (x : Finset (β ⊕ ℕ)) :
    (finsetModel β).up x = modelUp x := rfl

end GroupStructure

end Plurality
