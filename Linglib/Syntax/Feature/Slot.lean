module

public import Linglib.Core.Order.Flat
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Feature-checking slots

This file defines the checking slot of one feature dimension on an item and its valuation. The
slot is `absent` when the item lacks the dimension, `unvalued` when the item bears the dimension
without a value, and `valued v` when it bears the value `v`. A probe bears an unvalued slot, and a
nominal whose case has not been assigned bears an unvalued case slot.

A checking slot is a flat slot (`Core/Order/Flat.lean`) with a new bottom element, so its type is
`WithBot (Flat α)`. Its order is `absent < unvalued < valued v`, and distinct values are
incomparable.

The map `toFlat` forgets whether the dimension is borne: it sends `absent` and `unvalued` to `⊥`.
It has a left adjoint `ofFlat`, which sends `⊥` to `absent`, and a right adjoint, the coercion,
which sends `⊥` to `unvalued`. Both adjoints are sections of `toFlat`.

Valuing a slot with `v` unifies it with `valued v`. An unvalued slot becomes `valued v`, a slot
valued `v` is unchanged, and a slot valued `w ≠ v` fails, which is `⊤`. An absent slot is
unchanged, since an item that lacks a dimension cannot be valued in it. On a borne slot,
[valuation is flat unification](##FeatureSlot.map_toFlat_valueWith).

## Main definitions

* `FeatureSlot`: the checking slots with values in `α`.
* `FeatureSlot.toFlat`: the value of a slot as a flat slot.
* `FeatureSlot.ofFlat`: a flat slot as a checking slot.
* `FeatureSlot.gciOfFlat`: `ofFlat` and `toFlat` form a Galois coinsertion.
* `FeatureSlot.giToFlat`: `toFlat` and the coercion form a Galois insertion.
* `FeatureSlot.valueWith`: a slot valued with `v`.

## Implementation notes

`FeatureSlot α` unfolds to `Option (Option α)`, so the literal `none` typechecks as a slot and
denotes `absent`, not `unvalued`. Write the named slots.

## References

* [chomsky-2000]
-/

@[expose] public section

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

@[simp] theorem absent_ne_unvalued : (absent : FeatureSlot α) ≠ unvalued := nofun

@[simp] theorem unvalued_ne_valued (v : α) : unvalued ≠ valued v := nofun

instance [DecidableEq α] : DecidableEq (FeatureSlot α) :=
  inferInstanceAs (DecidableEq (WithBot (Flat α)))

instance (priority := 100) decidableEqAbsent : (s : FeatureSlot α) → Decidable (s = absent)
  | .absent => isTrue rfl
  | .unvalued => isFalse unvalued_ne_absent
  | .valued v => isFalse (valued_ne_absent v)

instance (priority := 100) decidableEqUnvalued : (s : FeatureSlot α) → Decidable (s = unvalued)
  | .absent => isFalse absent_ne_unvalued
  | .unvalued => isTrue rfl
  | .valued v => isFalse (valued_ne_unvalued v)

@[simp] theorem valued_inj {v w : α} : valued v = valued w ↔ v = w :=
  ⟨fun h ↦ Flat.coe_injective (WithBot.coe_injective h), fun h ↦ h ▸ rfl⟩

@[simp] theorem valued_le_iff {v : α} {s : FeatureSlot α} : valued v ≤ s ↔ s = valued v := by
  cases s with
  | absent => exact iff_of_false (WithBot.not_coe_le_bot _) (absent_ne_valued v)
  | unvalued => exact iff_of_false (fun h ↦ Flat.not_coe_le_bot v (WithBot.coe_le_coe.1 h)) nofun
  | valued w => simp [eq_comm]

/-- The value of a slot, if it is valued. -/
def value? : FeatureSlot α → Option α
  | .valued v => some v
  | _ => none

@[simp] theorem value?_absent : (absent : FeatureSlot α).value? = none := rfl

@[simp] theorem value?_unvalued : (unvalued : FeatureSlot α).value? = none := rfl

@[simp] theorem value?_valued (v : α) : (valued v).value? = some v := rfl

/-- A slot with its value, if any, sent through `g`. -/
def map {β : Type*} (g : α → β) : FeatureSlot α → FeatureSlot β
  | .absent => .absent
  | .unvalued => .unvalued
  | .valued v => .valued (g v)

@[simp] theorem map_absent {β : Type*} (g : α → β) : (absent : FeatureSlot α).map g = absent := rfl

@[simp] theorem map_unvalued {β : Type*} (g : α → β) :
    (unvalued : FeatureSlot α).map g = unvalued := rfl

@[simp] theorem map_valued {β : Type*} (g : α → β) (v : α) : (valued v).map g = valued (g v) :=
  rfl

@[simp] theorem map_eq_valued_iff {β : Type*} {g : α → β} {s : FeatureSlot α} {w : β} :
    s.map g = valued w ↔ ∃ v, s = valued v ∧ g v = w := by
  cases s <;> simp [map]

@[simp] theorem map_map {β γ : Type*} (g : α → β) (h : β → γ) (s : FeatureSlot α) :
    (s.map g).map h = s.map (h ∘ g) := by
  cases s <;> rfl

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

/-! ### Valuation -/

section Valuation

variable [DecidableEq α] {v w : α} {s s' : FeatureSlot α}

/-- The slot `s` valued with `v`, or `⊤` if `s` is valued otherwise. An absent slot is
unchanged. -/
def valueWith (v : α) (s : FeatureSlot α) : WithTop (FeatureSlot α) :=
  if s = absent then s else PartialUnify.unify s (valued v)

theorem valueWith_of_ne_absent (hs : s ≠ absent) :
    valueWith v s = PartialUnify.unify s (valued v) := by
  simp [valueWith, hs]

@[simp] theorem valueWith_absent (v : α) :
    valueWith v (absent : FeatureSlot α) = ↑(absent : FeatureSlot α) := by
  simp [valueWith]

@[simp] theorem valueWith_unvalued (v : α) :
    valueWith v (unvalued : FeatureSlot α) = valued v := by
  rw [valueWith_of_ne_absent unvalued_ne_absent]
  exact PartialUnify.unify_eq_right.2 (WithBot.coe_le_coe.2 bot_le)

@[simp] theorem valueWith_valued (v w : α) :
    valueWith v (valued w) = if w = v then ↑(valued w : FeatureSlot α) else ⊤ := by
  rw [valueWith_of_ne_absent (valued_ne_absent w)]
  split_ifs with h
  · exact h ▸ PartialUnify.unify_self _
  · simp [PartialUnify.unify_coe_coe,
      show PartialUnify.unify (w : Flat α) v = ⊤ from Flat.unify_eq_top_of_ne h]

theorem valueWith_eq_top_iff : valueWith v s = ⊤ ↔ ∃ w, w ≠ v ∧ s = valued w := by
  cases s with
  | absent => simp
  | unvalued => simp
  | valued w => by_cases h : w = v <;> simp [h]

theorem le_of_valueWith_eq_coe (h : valueWith v s = s') : s ≤ s' := by
  rcases eq_or_ne s absent with rfl | hs
  · exact bot_le
  · rw [valueWith_of_ne_absent hs, PartialUnify.unify_eq_coe_iff_isLUB] at h
    exact (mem_upperBounds_pair.1 h.1).1

theorem valueWith_mono (v : α) :
    Monotone (valueWith v : FeatureSlot α → WithTop (FeatureSlot α)) := by
  intro s s' h
  cases s with
  | absent => exact valueWith_absent v ▸ WithTop.coe_bot (α := FeatureSlot α) ▸ bot_le
  | unvalued =>
    cases s' with
    | absent => exact absurd h (WithBot.not_coe_le_bot _)
    | unvalued => exact le_rfl
    | valued w => by_cases hw : w = v <;> simp [hw]
  | valued u =>
    cases s' with
    | absent => exact absurd h (WithBot.not_coe_le_bot _)
    | unvalued => exact absurd (Flat.coe_le_iff.1 (WithBot.coe_le_coe.1 h)) (by simp)
    | valued w => obtain rfl : u = w := Flat.coe_le_coe.1 (WithBot.coe_le_coe.1 h); exact le_rfl

theorem map_toFlat_valueWith (hs : s ≠ absent) :
    (valueWith v s).map toFlat = PartialUnify.unify s.toFlat (v : Flat α) := by
  cases s with
  | absent => exact absurd rfl hs
  | unvalued =>
    rw [valueWith_unvalued, WithTop.map_coe, toFlat_valued, toFlat_unvalued, eq_comm]
    exact PartialUnify.unify_eq_right.2 bot_le
  | valued w =>
    rcases eq_or_ne w v with rfl | hwv
    · simp
    · rw [valueWith_eq_top_iff.2 ⟨w, hwv, rfl⟩, WithTop.map_top, toFlat_valued]
      exact (Flat.unify_eq_top_of_ne hwv).symm

end Valuation

end FeatureSlot
