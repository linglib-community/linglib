/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Order.Monotone.Defs

/-!
# Monotonicity markings

A monotonicity marking says how a function between preorders treats the order: `+` for a monotone
function, `−` for an antitone function, and `·` when nothing is known. A marking is a sign, `+`
being `1`, `−` being `-1` and `·` being `0`, and markings compose as signs multiply: a monotone
function after an antitone one is antitone, two antitone functions compose to a monotone one, and
a composite with an unmarked factor is unmarked.

The marking `m` lies below `m'` in the information order, `m ⊑ m'`, when `m = m'` or `m' = ·`.
This is the inclusion of the classes of functions: `m ⊑ m'` exactly when every function that
behaves as `m` says behaves as `m'` says.

## Main definitions

* `NaturalLogic.MonoBy`: a function is monotone under the marking `+`, antitone under `−`, and
  arbitrary under `·`.
* `NaturalLogic.MarkingLE`: the information order on markings.
* `NaturalLogic.markingSup`: the join of two markings in the information order.

## Main results

* `NaturalLogic.MonoBy.comp`: a composition behaves as the product of the markings of its factors.
* `NaturalLogic.markingLE_iff_forall_monoBy`: the information order is the inclusion of the
  classes of functions.

## Implementation notes

Markings are `SignType`, so that the composition of markings is the multiplication of signs. The
information order is a relation of its own, since `SignType` carries the order `-1 < 0 < 1`.

## References

* [icard-moss-tune-2017]
-/

@[expose] public section

namespace NaturalLogic

/-! ### The information order -/

/-- The information order on markings: `m ⊑ m'` when `m = m'` or `m'` is `·`. -/
def MarkingLE (m m' : SignType) : Prop := m = m' ∨ m' = 0

instance : DecidableRel MarkingLE := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem MarkingLE.refl (m : SignType) : MarkingLE m m := .inl rfl

theorem MarkingLE.trans {a b c : SignType} (h₁ : MarkingLE a b) (h₂ : MarkingLE b c) :
    MarkingLE a c := by
  revert h₁ h₂; decide +revert

theorem MarkingLE.antisymm {a b : SignType} (h₁ : MarkingLE a b) (h₂ : MarkingLE b a) : a = b := by
  revert h₁ h₂; decide +revert

theorem markingLE_zero (m : SignType) : MarkingLE m 0 := .inr rfl

/-- The join in the information order: `m ∨ m = m`, and `m ∨ m' = ·` when `m ≠ m'`. -/
def markingSup (m m' : SignType) : SignType := if m = m' then m else 0

@[simp] theorem markingSup_self (m : SignType) : markingSup m m = m := by simp [markingSup]

theorem markingLE_markingSup_left (m m' : SignType) : MarkingLE m (markingSup m m') := by
  revert m m'; decide

theorem markingLE_markingSup_right (m m' : SignType) : MarkingLE m' (markingSup m m') := by
  revert m m'; decide

theorem markingSup_le {a b c : SignType} (h₁ : MarkingLE a c) (h₂ : MarkingLE b c) :
    MarkingLE (markingSup a b) c := by
  revert h₁ h₂; decide +revert

/-! ### Functions that behave as a marking says -/

section MonoBy

variable {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] {m m' : SignType}

/-- A function behaves as the marking `m` says when it is monotone for `m = +` and antitone for
`m = −`; every function behaves as `·` says. -/
def MonoBy : SignType → (α → β) → Prop
  | .zero, _ => True
  | .pos, f => Monotone f
  | .neg, f => Antitone f

@[simp] theorem monoBy_zero {f : α → β} : MonoBy 0 f := trivial

@[simp] theorem monoBy_one {f : α → β} : MonoBy 1 f ↔ Monotone f := .rfl

@[simp] theorem monoBy_neg_one {f : α → β} : MonoBy (-1) f ↔ Antitone f := .rfl

/-- The composition of a function that behaves as `m` with one that behaves as `m'` behaves as
their product. -/
theorem MonoBy.comp {g : β → γ} {f : α → β} (hg : MonoBy m g) (hf : MonoBy m' f) :
    MonoBy (m * m') (g ∘ f) := by
  cases m <;> cases m'
  exacts [trivial, trivial, trivial, trivial, Antitone.comp (g := g) hg hf,
    Antitone.comp_monotone (g := g) hg hf, trivial, Monotone.comp_antitone (g := g) hg hf,
    Monotone.comp (g := g) hg hf]

theorem MonoBy.mono {f : α → β} (h : MarkingLE m m') (hf : MonoBy m f) : MonoBy m' f := by
  rcases h with rfl | rfl
  exacts [hf, trivial]

theorem MonoBy.conj {k : β → γ} {g : γ → δ} {f : α → β} (hk : MonoBy m k) (hg : Monotone g)
    (hf : Monotone f) : MonoBy m (g ∘ k ∘ f) := by
  simpa using (monoBy_one.2 hg).comp (hk.comp (monoBy_one.2 hf))

/-- The marking `m` lies below `m'` in the information order exactly when every function that
behaves as `m` says behaves as `m'` says. -/
theorem markingLE_iff_forall_monoBy :
    MarkingLE m m' ↔ ∀ f : Prop → Prop, MonoBy m f → MonoBy m' f := by
  refine ⟨fun h _ ↦ .mono h, fun h ↦ ?_⟩
  have hid : ¬Antitone (id : Prop → Prop) := fun h ↦ h (show False ≤ True from False.elim) trivial
  have hnot : ¬Monotone Not := fun h ↦ h (show False ≤ True from False.elim) id trivial
  have anti : Antitone Not := fun _ _ h hn ha ↦ hn (h ha)
  cases m <;> cases m'
  exacts [.inl rfl, absurd (h id trivial) hid, absurd (h Not trivial) hnot, .inr rfl, .inl rfl,
    absurd (h Not anti) hnot, .inr rfl, absurd (h id monotone_id) hid, .inl rfl]

end MonoBy

end NaturalLogic
