module

public import Linglib.Core.Order.Flat
public import Mathlib.Order.GaloisConnection.Defs
public import Mathlib.Order.WithBot

/-!
# Feature-checking slots

A feature-checking slot records the state of one feature dimension on a lexical item. Under
Agree a dimension is in one of three states: `absent`, when the item lacks it; `unvalued`, a
probe, present but valueless (Chomsky's unvalued feature, which searches for a goal); and
`valued v`. A determinate slot of `Core/Order/Flat.lean` has two states, bottom or a value, so a
checking slot is a flat slot with a new bottom below it: `WithBot (Flat α)`, as `EReal` is
`WithBot (WithTop ℝ)`. Its subsumption order is therefore `absent < unvalued < valued v` with
distinct values incomparable, the per-slot order the bundle subsumption order is built from.

Following Marcolli, Chomsky and Berwick, the free-Merge core keeps the features of a syntactic
object atomic, and the valued/unvalued apparatus belongs to the Agree layer, so slots are kept
general here, polymorphic in the value type, and decoupled from the `SyntacticObject` carrier.

## Main definitions

* `Minimalist.FeatureSlot` — `WithBot (Flat α)`, with the patterns `absent`, `unvalued`,
  `valued` and the eliminator `FeatureSlot.rec'`
* `Minimalist.FeatureSlot.valueWith` — valuation, unification of a present slot with a value,
  `⊤` on a clash
* `Minimalist.FeatureSlot.ofFlat`, `Minimalist.FeatureSlot.toFlat`,
  `Minimalist.FeatureSlot.gciOfFlat` — the checking slot over the flat slot, a Galois
  coinsertion; on a borne slot valuation restricts to flat unification
  (`FeatureSlot.map_toFlat_valueWith`)

## References

* [chomsky-2000]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

/-- A feature-checking slot for value type `α` is `absent`, `unvalued` (a probe), or `valued v`:
a flat slot with a new bottom below it. -/
abbrev FeatureSlot (α : Type*) := WithBot (Flat α)

namespace FeatureSlot

variable {α : Type*}

/-- An item lacking the dimension has the `absent` slot. -/
@[match_pattern] abbrev absent : FeatureSlot α := none

/-- A probe has the `unvalued` slot, present but valueless. -/
@[match_pattern] abbrev unvalued : FeatureSlot α := WithBot.some ⊥

/-- The `valued v` slot carries the value `v`. -/
@[match_pattern] abbrev valued (v : α) : FeatureSlot α := WithBot.some (Flat.some v)

/-- A slot is absent, unvalued, or valued. -/
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

/-- The slot specifies a present feature, that is, it is not `absent`. -/
def isSpecified : FeatureSlot α → Bool
  | absent => false
  | _ => true

/-- The slot is a probe (present but unvalued). -/
def isUnvalued : FeatureSlot α → Bool
  | unvalued => true
  | _ => false

/-- The slot carries a value. -/
def isValued : FeatureSlot α → Bool
  | valued _ => true
  | _ => false

/-- The value of a slot, when it is valued. -/
def value? : FeatureSlot α → Option α
  | valued v => some v
  | _ => none

/-! ### The flat slot underneath -/

/-- A flat slot as a checking slot, borne exactly when specified: `⊥` becomes `absent` and a
value is `valued`. -/
def ofFlat : Flat α → FeatureSlot α := Flat.recBotCoe absent valued

/-- The value content of a checking slot: `absent` and `unvalued` alike are unspecified. -/
def toFlat : FeatureSlot α → Flat α := WithBot.recBotCoe ⊥ id

@[simp] theorem ofFlat_bot : ofFlat (⊥ : Flat α) = absent := rfl

@[simp] theorem ofFlat_coe (v : α) : ofFlat (v : Flat α) = valued v := rfl

@[simp] theorem toFlat_absent : toFlat (absent : FeatureSlot α) = ⊥ := rfl

@[simp] theorem toFlat_unvalued : toFlat (unvalued : FeatureSlot α) = ⊥ := rfl

@[simp] theorem toFlat_valued (v : α) : toFlat (valued v) = ↑v := rfl

@[simp] theorem toFlat_ofFlat (x : Flat α) : toFlat (ofFlat x) = x := by
  induction x using Flat.recBotCoe <;> rfl

theorem gc_ofFlat_toFlat : GaloisConnection (ofFlat : Flat α → FeatureSlot α) toFlat := by
  intro x s
  cases s with
  | absent =>
    induction x using Flat.recBotCoe with
    | bot => simp
    | coe v =>
      exact iff_of_false (fun h ↦ valued_ne_absent v (le_bot_iff.1 h)) (by simp [le_bot_iff])
  | unvalued =>
    induction x using Flat.recBotCoe with
    | bot => exact iff_of_true bot_le bot_le
    | coe v =>
      refine iff_of_false (fun h ↦ ?_) (by simp [le_bot_iff])
      have := WithBot.coe_le_coe.1 h
      simp [le_bot_iff] at this
  | valued w =>
    induction x using Flat.recBotCoe with
    | bot => exact iff_of_true bot_le bot_le
    | coe v =>
      simp only [ofFlat_coe, toFlat_valued]
      exact WithBot.coe_le_coe

/-- The checking layer sits over the flat layer by a Galois coinsertion. -/
def gciOfFlat : GaloisCoinsertion (ofFlat : Flat α → FeatureSlot α) toFlat :=
  gc_ofFlat_toFlat.toGaloisCoinsertion fun x ↦ (toFlat_ofFlat x).le

/-- Valuing a slot with `v` unifies it with `valued v` when the item bears the dimension: an
unvalued slot takes `v`, a slot valued `v` stays, and a slot valued otherwise clashes, `⊤`. An absent
slot stays absent. -/
def valueWith [DecidableEq α] (v : α) (s : FeatureSlot α) : WithTop (FeatureSlot α) :=
  if s = absent then s else PartialUnify.unify s (valued v)

section Valuation

variable [DecidableEq α] {v w : α} {s s' : FeatureSlot α}

@[simp] theorem valueWith_absent (v : α) :
    valueWith v (absent : FeatureSlot α) = ↑(absent : FeatureSlot α) := by
  simp [valueWith]

@[simp] theorem valueWith_unvalued (v : α) :
    valueWith v (unvalued : FeatureSlot α) = valued v := by
  simp only [valueWith, unvalued_ne_absent, ↓reduceIte]
  exact PartialUnify.unify_eq_right.2 (WithBot.coe_le_coe.2 bot_le)

@[simp] theorem valueWith_valued (v w : α) :
    valueWith v (valued w) = if w = v then ↑(valued w : FeatureSlot α) else ⊤ := by
  simp only [valueWith, valued_ne_absent, ↓reduceIte]
  split_ifs with h
  · subst h
    exact PartialUnify.unify_self _
  · refine PartialUnify.unify_eq_top_iff.2 fun ⟨u, hu⟩ ↦ h ?_
    obtain ⟨h1, h2⟩ := mem_upperBounds_pair.1 hu
    obtain ⟨f, rfl, hf⟩ := WithBot.coe_le_iff.1 h1
    exact Flat.coe_inj.1 ((Flat.coe_le_iff.1 hf).symm.trans
      (Flat.coe_le_iff.1 (WithBot.coe_le_coe.1 h2)))

theorem isLUB_of_valueWith_eq_coe (hs : s ≠ absent) (h : valueWith v s = s') :
    IsLUB {s, valued v} s' := by
  simp only [valueWith, hs, ↓reduceIte] at h
  exact PartialUnify.isLUB_of_unify_eq_coe h

theorem valueWith_eq_top_iff_not_bddAbove (hs : s ≠ absent) :
    valueWith v s = ⊤ ↔ ¬ BddAbove ({s, valued v} : Set (FeatureSlot α)) := by
  simp only [valueWith, hs, ↓reduceIte]
  exact PartialUnify.unify_eq_top_iff

theorem valueWith_eq_top_iff : valueWith v s = ⊤ ↔ ∃ w, w ≠ v ∧ s = valued w := by
  cases s with
  | absent => simp
  | unvalued => simp
  | valued w => by_cases h : w = v <;> simp [h]

theorem le_of_valueWith_eq_coe (h : valueWith v s = s') : s ≤ s' := by
  cases s with
  | absent => exact bot_le
  | unvalued =>
    obtain rfl : valued v = s' := WithTop.coe_inj.1 (by simpa using h)
    exact WithBot.coe_le_coe.2 bot_le
  | valued w =>
    by_cases hw : w = v
    · subst hw
      obtain rfl : valued w = s' := WithTop.coe_inj.1 (by simpa using h)
      exact le_rfl
    · simp [hw] at h

theorem valueWith_mono (v : α) :
    Monotone (valueWith v : FeatureSlot α → WithTop (FeatureSlot α)) := by
  intro s s' h
  cases s with
  | absent =>
    rw [valueWith_absent]
    exact (WithTop.coe_bot (α := FeatureSlot α)) ▸ bot_le
  | unvalued =>
    cases s' with
    | absent => exact absurd h (WithBot.not_coe_le_bot _)
    | unvalued => exact le_rfl
    | valued w => by_cases hw : w = v <;> simp [hw]
  | valued u =>
    cases s' with
    | absent => exact absurd h (WithBot.not_coe_le_bot _)
    | unvalued => exact absurd (Flat.coe_le_iff.1 (WithBot.coe_le_coe.1 h)) (by simp)
    | valued w =>
      obtain rfl : u = w := Flat.coe_le_coe.1 (WithBot.coe_le_coe.1 h)
      exact le_rfl

/-- On a borne slot, valuation restricts to flat unification: the `WithBot` refinement adds
exactly the absence guard. -/
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

@[simp] theorem isSpecified_iff_ne_bot {s : FeatureSlot α} :
    s.isSpecified = true ↔ s ≠ ⊥ := by
  cases s with
  | absent => simp [isSpecified]
  | unvalued => exact ⟨fun _ ↦ nofun, fun _ ↦ rfl⟩
  | valued v => exact ⟨fun _ ↦ nofun, fun _ ↦ rfl⟩

end FeatureSlot

end Minimalist
