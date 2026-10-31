module

public import Linglib.Core.Order.Flat
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Feature-checking slots

This file defines the checking slot of one feature dimension on a lexical item. The slot is
`absent` when the item lacks the dimension, `unvalued` when the item bears the dimension without a
value, as a probe does, and `valued v` when it bears the value `v`.

A checking slot is a flat slot (`Core/Order/Flat.lean`) with a new bottom element, so its type is
`WithBot (Flat α)`. Its order is `absent < unvalued < valued v`, and distinct values are
incomparable.

The map `toFlat` forgets whether the dimension is borne: it sends `absent` and `unvalued` to `⊥`.
It has a left adjoint `ofFlat`, which sends `⊥` to `absent`, and a right adjoint, the coercion,
which sends `⊥` to `unvalued`. Both adjoints are sections of `toFlat`.

## Main definitions

* `Minimalist.FeatureSlot`: the checking slots with values in `α`.
* `Minimalist.FeatureSlot.toFlat`: the value of a slot as a flat slot.
* `Minimalist.FeatureSlot.ofFlat`: a flat slot as a checking slot.
* `Minimalist.FeatureSlot.gciOfFlat`: `ofFlat` and `toFlat` form a Galois coinsertion.
* `Minimalist.FeatureSlot.giToFlat`: `toFlat` and the coercion form a Galois insertion.

## Implementation notes

The leaves of a `SyntacticObject` are lexical-item tokens, and the tree records nothing else: in
[marcolli-chomsky-berwick-2025] the leaves are drawn from a set of lexical items and syntactic
features, and Merge attaches no label to an internal vertex. Agree changes the features of the
items it relates, producing what [chomsky-2000] calls modified lexical items. Slots are therefore
kept outside the tree: the state of Agree (`Minimalist.FeatureState`) assigns a bundle of slots to
each item, and valuation changes that assignment, not the tree.

## TODO

`LexicalItem.wh` should be read from the [wh] slot of the item's bundle.

## References

* [chomsky-2000]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

/-- A checking slot with values in `α`: `absent`, `unvalued`, or `valued v`. -/
abbrev FeatureSlot (α : Type*) := WithBot (Flat α)

namespace FeatureSlot

variable {α : Type*}

/-- The slot of an item that lacks the dimension. -/
@[match_pattern] abbrev absent : FeatureSlot α := none

/-- The slot of an item that bears the dimension without a value. -/
@[match_pattern] abbrev unvalued : FeatureSlot α := WithBot.some ⊥

/-- The slot of an item that bears the value `v`. -/
@[match_pattern] abbrev valued (v : α) : FeatureSlot α := WithBot.some (Flat.some v)

/-- Case analysis on a slot. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec' {motive : FeatureSlot α → Sort*} (absent : motive .absent) (unvalued : motive .unvalued)
    (valued : ∀ v, motive (.valued v)) : ∀ s, motive s
  | .absent => absent
  | .unvalued => unvalued
  | .valued v => valued v

@[simp] theorem bot_eq_absent : (⊥ : FeatureSlot α) = absent := rfl

@[simp] theorem unvalued_ne_absent : (unvalued : FeatureSlot α) ≠ absent := nofun

@[simp] theorem valued_ne_absent (v : α) : valued v ≠ absent := nofun

@[simp] theorem absent_ne_valued (v : α) : absent ≠ valued v := nofun

@[simp] theorem valued_ne_unvalued (v : α) : valued v ≠ unvalued := nofun

@[simp] theorem valued_inj {v w : α} : valued v = valued w ↔ v = w :=
  ⟨fun h ↦ Flat.coe_injective (WithBot.coe_injective h), fun h ↦ h ▸ rfl⟩

@[simp] theorem valued_le_iff {v : α} {s : FeatureSlot α} : valued v ≤ s ↔ s = valued v := by
  cases s with
  | absent => exact iff_of_false (WithBot.not_coe_le_bot _) (absent_ne_valued v)
  | unvalued => exact iff_of_false (fun h ↦ Flat.not_coe_le_bot v (WithBot.coe_le_coe.1 h)) nofun
  | valued w => simp [eq_comm]

/-! ### The flat slot underneath -/

/-- The value of a slot as a flat slot, `⊥` if the slot is absent or unvalued. -/
def toFlat : FeatureSlot α → Flat α := WithBot.unbotD ⊥

/-- A flat slot as a checking slot, absent where the flat slot is `⊥`. -/
def ofFlat : Flat α → FeatureSlot α := Flat.recBotCoe absent valued

@[simp] theorem ofFlat_bot : ofFlat (⊥ : Flat α) = absent := rfl

@[simp] theorem ofFlat_coe (v : α) : ofFlat (v : Flat α) = valued v := rfl

@[simp] theorem toFlat_absent : toFlat (absent : FeatureSlot α) = ⊥ := rfl

@[simp] theorem toFlat_unvalued : toFlat (unvalued : FeatureSlot α) = ⊥ := rfl

@[simp] theorem toFlat_valued (v : α) : toFlat (valued v) = ↑v := rfl

@[simp] theorem toFlat_coe (x : Flat α) : toFlat (x : FeatureSlot α) = x := rfl

@[simp] theorem toFlat_ofFlat (x : Flat α) : toFlat (ofFlat x) = x := by
  induction x using Flat.recBotCoe <;> rfl

theorem gc_ofFlat_toFlat : GaloisConnection (ofFlat : Flat α → FeatureSlot α) toFlat := by
  intro x s
  induction x using Flat.recBotCoe with
  | bot => exact iff_of_true bot_le bot_le
  | coe v =>
    rcases eq_or_ne s ⊥ with rfl | hs
    · exact iff_of_false (WithBot.not_coe_le_bot _) (Flat.not_coe_le_bot v)
    · exact (WithBot.le_unbotD_iff hs).symm

/-- `ofFlat` and `toFlat` form a Galois coinsertion. -/
def gciOfFlat : GaloisCoinsertion (ofFlat : Flat α → FeatureSlot α) toFlat :=
  gc_ofFlat_toFlat.toGaloisCoinsertion fun x ↦ (toFlat_ofFlat x).le

/-- `toFlat` and the coercion form a Galois insertion. -/
def giToFlat : GaloisInsertion (toFlat : FeatureSlot α → Flat α) (↑) :=
  WithBot.giUnbotDBot

end FeatureSlot

end Minimalist
