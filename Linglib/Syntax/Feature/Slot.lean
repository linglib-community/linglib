module

public import Linglib.Core.Order.Flat
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Feature-checking slots

This file defines the checking slot of one feature dimension on an item. For a slot order `β`,
the order of the information an item can hold in the dimension, the checking slot is
`FeatureSlot β = WithBot β`: the new bottom element is the slot of an item that lacks the
dimension, `absent`, and `↑x` is the slot of an item that bears the dimension and holds `x`,
`unvalued` when `x = ⊥`. A probe bears an unvalued slot, and a nominal whose case has not been
assigned bears an unvalued case slot.

Over a flat slot (`Core/Order/Flat.lean`), a slot is `absent`, `unvalued`, or `valued v`, with
`absent < unvalued < valued v` and distinct values incomparable. Over an order with more
structure, such as that of person specifications, a slot that holds some information can come
to hold more.

Forgetting whether the dimension is borne is `WithBot.unbotD ⊥`, which sends the absent and the
unvalued slot to `⊥`. Its left adjoint `FeatureSlot.ofSlot` sends `⊥` to the absent slot
(`FeatureSlot.gc_ofSlot_unbotD`), and its right adjoint is the coercion (mathlib's
`WithBot.giUnbotDBot`).

Unifying a slot with `x` by a unification `u` of `β` is `FeatureSlot.unifyWith u x`. An absent
slot is unchanged, since an item that lacks a dimension cannot be valued in it. Where `u`
computes the joins of `β`, unifying a borne slot with `x` is their join
(`FeatureSlot.unifyWith_eq_coe_iff`), and forgetting that the slot is borne gives the
unification in `β` (`FeatureSlot.map_unbotD_unifyWith`).

## Implementation notes

`FeatureSlot (Flat α)` unfolds to `Option (Option α)`, so the literal `none` typechecks as a slot
and denotes `absent`, not `unvalued`. Write the named slots.

The slot takes its order as the parameter, not a type of values, so that a dimension whose
information is not flat has a checking slot of the same kind. A flat dimension is the case
`β = Flat α`.

## References

* [chomsky-2000]
-/

@[expose] public section

/-- A checking slot over the slot order `β`: absent, or borne with the information `x : β`,
unvalued when `x = ⊥`. Over a flat slot it is `absent`, `unvalued`, or `valued v`. -/
abbrev FeatureSlot (β : Type*) := WithBot β

namespace FeatureSlot

variable {α β : Type*}

/-- The slot of an item that lacks the dimension. -/
@[match_pattern] abbrev absent : FeatureSlot β := none

/-- The slot of an item that bears the dimension without a value. -/
@[match_pattern] abbrev unvalued [Bot β] : FeatureSlot β := WithBot.some ⊥

/-- The slot of an item that bears the value `v`. -/
@[match_pattern] abbrev valued (v : α) : FeatureSlot (Flat α) := WithBot.some (Flat.some v)

/-- Case analysis on a slot. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def rec' {motive : FeatureSlot (Flat α) → Sort*} (absent : motive .absent)
    (unvalued : motive .unvalued) (valued : ∀ v, motive (.valued v)) : ∀ s, motive s
  | .absent => absent
  | .unvalued => unvalued
  | .valued v => valued v

@[simp] theorem bot_eq_absent : (⊥ : FeatureSlot (Flat α)) = absent := rfl

@[simp] theorem unvalued_ne_absent : (unvalued : FeatureSlot (Flat α)) ≠ absent := nofun

@[simp] theorem valued_ne_absent (v : α) : valued v ≠ absent := nofun

@[simp] theorem absent_ne_valued (v : α) : absent ≠ valued v := nofun

@[simp] theorem valued_ne_unvalued (v : α) : valued v ≠ unvalued := nofun

@[simp] theorem absent_ne_unvalued : (absent : FeatureSlot (Flat α)) ≠ unvalued := nofun

@[simp] theorem unvalued_ne_valued (v : α) : unvalued ≠ valued v := nofun

instance [DecidableEq α] : DecidableEq (FeatureSlot (Flat α)) :=
  inferInstanceAs (DecidableEq (WithBot (Flat α)))

instance (priority := 100) decidableEqAbsent : (s : FeatureSlot (Flat α)) → Decidable (s = absent)
  | .absent => isTrue rfl
  | .unvalued => isFalse unvalued_ne_absent
  | .valued v => isFalse (valued_ne_absent v)

instance (priority := 100) decidableEqUnvalued :
    (s : FeatureSlot (Flat α)) → Decidable (s = unvalued)
  | .absent => isFalse absent_ne_unvalued
  | .unvalued => isTrue rfl
  | .valued v => isFalse (valued_ne_unvalued v)

@[simp] theorem valued_inj {v w : α} : valued v = valued w ↔ v = w :=
  ⟨fun h ↦ Flat.coe_injective (WithBot.coe_injective h), fun h ↦ h ▸ rfl⟩

@[simp] theorem valued_le_iff {v : α} {s : FeatureSlot (Flat α)} : valued v ≤ s ↔ s = valued v := by
  cases s with
  | absent => exact iff_of_false (WithBot.not_coe_le_bot _) (absent_ne_valued v)
  | unvalued => exact iff_of_false (fun h ↦ Flat.not_coe_le_bot v (WithBot.coe_le_coe.1 h)) nofun
  | valued w => simp [eq_comm]

/-- The value of a slot, if it is valued. -/
def value? : FeatureSlot (Flat α) → Option α
  | .valued v => some v
  | _ => none

@[simp] theorem value?_absent : (absent : FeatureSlot (Flat α)).value? = none := rfl

@[simp] theorem value?_unvalued : (unvalued : FeatureSlot (Flat α)).value? = none := rfl

@[simp] theorem value?_valued (v : α) : (valued v).value? = some v := rfl

/-- The slot an unvalued item has once offered `o`: valued if `o` is a value, unvalued otherwise. -/
def offer (o : Option α) : FeatureSlot (Flat α) := o.elim .unvalued .valued

@[simp] theorem offer_none : offer (none : Option α) = .unvalued := rfl

@[simp] theorem offer_some (v : α) : offer (some v) = .valued v := rfl

@[simp] theorem offer_eq_valued_iff {o : Option α} {v : α} : offer o = .valued v ↔ o = some v := by
  cases o <;> simp

@[simp] theorem offer_ne_absent (o : Option α) : offer o ≠ .absent := by
  cases o <;> simp

@[simp] theorem value?_offer (o : Option α) : (offer o).value? = o := by
  cases o <;> rfl

@[simp] theorem unvalued_le_valued (v : α) : (unvalued : FeatureSlot (Flat α)) ≤ valued v :=
  WithBot.coe_le_coe.2 bot_le

theorem unvalued_le_offer (o : Option α) : (unvalued : FeatureSlot (Flat α)) ≤ offer o := by
  cases o <;> simp

/-- A slot with its value, if any, sent through `g`. -/
def map (g : α → β) : FeatureSlot (Flat α) → FeatureSlot (Flat β)
  | .absent => .absent
  | .unvalued => .unvalued
  | .valued v => .valued (g v)

@[simp] theorem map_absent (g : α → β) : (absent : FeatureSlot (Flat α)).map g = absent := rfl

@[simp] theorem map_unvalued (g : α → β) :
    (unvalued : FeatureSlot (Flat α)).map g = unvalued := rfl

@[simp] theorem map_valued (g : α → β) (v : α) : (valued v).map g = valued (g v) :=
  rfl

@[simp] theorem map_eq_valued_iff {g : α → β} {s : FeatureSlot (Flat α)} {w : β} :
    s.map g = valued w ↔ ∃ v, s = valued v ∧ g v = w := by
  cases s <;> simp [map]

@[simp] theorem map_eq_unvalued_iff {g : α → β} {s : FeatureSlot (Flat α)} :
    s.map g = unvalued ↔ s = unvalued := by
  cases s <;> simp [map]

@[simp] theorem value?_map (g : α → β) (s : FeatureSlot (Flat α)) :
    (s.map g).value? = s.value?.map g := by
  cases s <;> rfl

@[simp] theorem map_offer (g : α → β) (o : Option α) :
    (offer o).map g = offer (o.map g) := by
  cases o <;> rfl

@[simp] theorem map_map {β γ : Type*} (g : α → β) (h : β → γ) (s : FeatureSlot (Flat α)) :
    (s.map g).map h = s.map (h ∘ g) := by
  cases s <;> rfl

/-! ### Slots over an arbitrary order -/

section Order

/-- The least checking slot holding `x`, absent where `x` is `⊥`. -/
def ofSlot [Bot β] [DecidableEq β] (x : β) : FeatureSlot β := if x = ⊥ then ⊥ else ↑x

@[simp] theorem ofSlot_bot [Bot β] [DecidableEq β] : ofSlot (⊥ : β) = ⊥ := by simp [ofSlot]

theorem ofSlot_of_ne_bot [Bot β] [DecidableEq β] {x : β} (h : x ≠ ⊥) : ofSlot x = ↑x := by
  simp [ofSlot, h]

@[simp] theorem unbotD_ofSlot [Bot β] [DecidableEq β] (x : β) :
    (ofSlot x).unbotD ⊥ = x := by
  by_cases h : x = ⊥
  · rw [h, ofSlot_bot, WithBot.unbotD_bot]
  · rw [ofSlot_of_ne_bot h, WithBot.unbotD_coe]

theorem gc_ofSlot_unbotD [PartialOrder β] [OrderBot β] [DecidableEq β] :
    GaloisConnection (ofSlot : β → FeatureSlot β) (WithBot.unbotD ⊥) := by
  intro x s
  by_cases h : x = ⊥
  · rw [h, ofSlot_bot]
    exact iff_of_true bot_le bot_le
  · rw [ofSlot_of_ne_bot h]
    induction s using WithBot.recBotCoe with
    | bot => exact iff_of_false (WithBot.not_coe_le_bot _) fun h' ↦ h (le_bot_iff.1 h')
    | coe y => exact WithBot.coe_le_coe

/-- `ofSlot` and `WithBot.unbotD ⊥` form a Galois coinsertion. -/
def gciOfSlot [PartialOrder β] [OrderBot β] [DecidableEq β] :
    GaloisCoinsertion (ofSlot : β → FeatureSlot β) (WithBot.unbotD ⊥) :=
  gc_ofSlot_unbotD.toGaloisCoinsertion fun x ↦ (unbotD_ofSlot x).le

/-- The slot `s` unified with `x` by the unification `u` of `β`, `⊤` where it fails. An absent
slot is unchanged. -/
def unifyWith (u : β → β → WithTop β) (x : β) : FeatureSlot β → WithTop (FeatureSlot β)
  | ⊥ => ((⊥ : FeatureSlot β) : WithTop (FeatureSlot β))
  | (y : β) => (u y x).map (↑)

variable {u : β → β → WithTop β} {x y : β} {s s' : FeatureSlot β}

@[simp] theorem unifyWith_bot : unifyWith u x ⊥ = ((⊥ : FeatureSlot β) : WithTop (FeatureSlot β)) :=
  rfl

@[simp] theorem unifyWith_coe : unifyWith u x (y : FeatureSlot β) = (u y x).map (↑) := rfl

theorem isLUB_pair_coe_iff [Preorder β] {z : β} :
    IsLUB ({↑y, ↑x} : Set (FeatureSlot β)) (z : FeatureSlot β) ↔ IsLUB {y, x} z := by
  simp only [isLUB_pair_iff_forall_le, WithBot.coe_le_coe]
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦
    ⟨fun h w hy hx ↦ WithBot.coe_le_coe.1 (h w (WithBot.coe_le_coe.2 hy) (WithBot.coe_le_coe.2 hx)),
      fun h w hy hx ↦ ?_⟩
  obtain ⟨w, rfl, -⟩ := WithBot.coe_le_iff.1 hy
  exact WithBot.coe_le_coe.2 (h w (WithBot.coe_le_coe.1 hy) (WithBot.coe_le_coe.1 hx))

/-- Where `u` computes the joins of `β`, unifying a slot the item bears with `x` is their join. -/
theorem unifyWith_eq_coe_iff [PartialOrder β]
    (hu : ∀ a b, IsLUB ({↑a, ↑b} : Set (WithTop β)) (u a b)) (hs : s ≠ ⊥) :
    unifyWith u x s = ↑s' ↔ IsLUB {s, (x : FeatureSlot β)} s' := by
  induction s using WithBot.recBotCoe with
  | bot => exact absurd rfl hs
  | coe y =>
    rw [unifyWith_coe, WithTop.map_eq_some_iff]
    refine ⟨fun ⟨z, hz, hzs⟩ ↦
      hzs ▸ isLUB_pair_coe_iff.2 ((WithTop.eq_coe_iff_of_isLUB (hu y x)).1 hz), fun h ↦ ?_⟩
    obtain ⟨z, rfl, -⟩ := WithBot.coe_le_iff.1 (isLUB_pair_iff_forall_le.1 h).1
    exact ⟨z, (WithTop.eq_coe_iff_of_isLUB (hu y x)).2 (isLUB_pair_coe_iff.1 h), rfl⟩

/-- Unifying a slot the item bears, then forgetting that it is borne, is unifying in `β`. -/
theorem map_unbotD_unifyWith [Bot β] (hs : s ≠ ⊥) :
    (unifyWith u x s).map (WithBot.unbotD ⊥) = u (s.unbotD ⊥) x := by
  induction s using WithBot.recBotCoe with
  | bot => exact absurd rfl hs
  | coe y =>
    rw [unifyWith_coe, WithBot.unbotD_coe]
    induction u y x using WithTop.recTopCoe <;> rfl

end Order

end FeatureSlot
