/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Connectives
public import Linglib.Logic.Bilattice.Involution
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# The knowledge order on three-valued truth

The three truth values are ordered by truth, with false below undefined and undefined below true.
They can also be ordered by how much they say. In the **knowledge order** undefined is below both
true and false, since it says nothing, and true and false are incomparable, since neither says more
than the other. Kleene's negation and his strong conjunction and disjunction respect this order: a
compound with better-informed parts is at least as well informed. This is Kleene's regularity
condition. The Weak Kleene connectives fail even the matching condition for the truth order. The
knowledge order has meets and a bottom but no top, since no value says both true and false; Belnap's
four values add one, and Kleene's three are their consistent part.

## Main definitions

* the `PartialOrder`, `OrderBot` and `SemilatticeInf` instances on `Know Trivalent`.

## Main results

* `Trivalent.kLE_iff`: the knowledge order, characterized.
* `Trivalent.truthOrder_ne_knowledgeOrder`: the two orders differ.
* the `Negation Trivalent` instance, `Trivalent.inf_kLE_inf_left`, `Trivalent.sup_kLE_sup_left`: the
  Strong Kleene connectives are knowledge-monotone.
* `Trivalent.kLE_ofProp_eq_true`: Bochvar's assertion operator only adds information.
* `Trivalent.transplication_kLE`: transplication only removes it.
* `Trivalent.meetWeak_not_truthMono`, `Trivalent.joinWeak_not_truthMono`: the Weak Kleene ones are
  not truth-monotone.
* `Trivalent.toKnow_supervaluation`: over a nonempty family, the supervaluation is the knowledge
  meet of the classical values, so shrinking the family can only add information
(`Trivalent.supervaluation_kLE_supervaluation`).

## Implementation notes

The knowledge order `≤ₖ` is carried by the synonym `Know Trivalent`, as in
`Logic/Bilattice/Defs.lean`.

## References

* [kleene-1952]
-/

@[expose] public section

namespace Trivalent

open Bilattice

/-!
### The knowledge order

One value is below another in the knowledge order when the second says everything the first does.
Undefined says nothing and is below every value. True and false each say one thing, and each is
below itself only.
-/

/-- One truth value is below another in the **knowledge order** when it is undefined or the two are
equal. Undefined is therefore below every value, and true and false are incomparable. -/
protected inductive KLE : Trivalent → Trivalent → Prop
  | undefined (a) : Trivalent.KLE .undefined a
  | refl (a) : Trivalent.KLE a a

instance : DecidableRel Trivalent.KLE := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor!) | exact isFalse (by rintro ⟨_⟩)

instance : Fintype (Know Trivalent) := inferInstanceAs (Fintype Trivalent)

instance : LE (Know Trivalent) := ⟨fun a b ↦ Trivalent.KLE (ofKnow a) (ofKnow b)⟩

instance : DecidableLE (Know Trivalent) := fun a b ↦
  inferInstanceAs (Decidable (Trivalent.KLE (ofKnow a) (ofKnow b)))

instance : PartialOrder (Know Trivalent) where
  le_refl _ := KLE.refl _
  le_trans := by decide
  le_antisymm := by decide

instance : OrderBot (Know Trivalent) where
  bot := toKnow .undefined
  bot_le _ := KLE.undefined _

instance : SemilatticeInf (Know Trivalent) where
  inf a b := if a = b then a else ⊥
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

theorem kLE_iff {a b : Trivalent} : a ≤ₖ b ↔ a = .undefined ∨ a = b := by
  cases a <;> cases b <;> decide

@[simp] theorem undefined_kLE (a : Trivalent) : .undefined ≤ₖ a := KLE.undefined a

/-- One value carries at most the information of another exactly when the second is true if the
first is, and false if the first is. -/
theorem kLE_iff_eq_true_imp_eq_false_imp {a b : Trivalent} :
    a ≤ₖ b ↔ (a = .true → b = .true) ∧ (a = .false → b = .false) := by
  rw [kLE_iff]; cases a <;> cases b <;> decide

/-- The truth order and the knowledge order differ, since false is below undefined in the truth
order and not in the knowledge order. -/
theorem truthOrder_ne_knowledgeOrder :
    Trivalent.false ≤ .undefined ∧ ¬ Trivalent.false ≤ₖ .undefined := by decide

/-- Kleene's negation respects the knowledge order, which makes it regular in Kleene's sense. It is
the only extension of classical negation that does. -/
instance : Negation Trivalent := ⟨by decide⟩

/-- Strong Kleene conjunction respects the knowledge order in each conjunct, so it is regular. -/
theorem inf_kLE_inf_left {a a' : Trivalent} (b : Trivalent) (h : a ≤ₖ a') : a ⊓ b ≤ₖ a' ⊓ b := by
  revert h; cases a <;> cases a' <;> cases b <;> decide

/-- Strong Kleene disjunction respects the knowledge order in each disjunct, so it is regular. -/
theorem sup_kLE_sup_left {a a' : Trivalent} (b : Trivalent) (h : a ≤ₖ a') : a ⊔ b ≤ₖ a' ⊔ b := by
  revert h; cases a <;> cases a' <;> cases b <;> decide

/-- Bochvar's assertion of a value carries at least the information of the value, so asserting only
adds information. -/
theorem kLE_ofProp_eq_true (a : Trivalent) : a ≤ₖ ofProp (a = .true) := by
  cases a <;> decide

/-- A value carries at most the information of a two-valued proposition's value exactly when, if it
is defined, it is true just in case the proposition holds. -/
theorem kLE_ofProp_iff {a : Trivalent} {P : Prop} [Decidable P] :
    a ≤ₖ ofProp P ↔ (a ≠ .undefined → (a = .true ↔ P)) := by
  rw [kLE_iff]; by_cases h : P <;> cases a <;> simp [h]

/-- *φ* presupposing *π* carries at most the information of *φ*, so adding a presupposition only
removes information. -/
theorem transplication_kLE (a b : Trivalent) : transplication a b ≤ₖ b := by
  cases a <;> first | exact kLE_refl b | exact undefined_kLE b

/-- Weak Kleene conjunction is not monotone in the truth order. Undefined is below true, yet the
weak conjunction of undefined with false is undefined, which is not below the weak conjunction of
true with false, namely false. Unlike the Strong Kleene conjunction, it is not an operation of a
bilattice. -/
theorem meetWeak_not_truthMono :
    ¬ ∀ a a' b : Trivalent, a ≤ a' → meetWeak a b ≤ meetWeak a' b :=
  fun h ↦ absurd (h .undefined .true .false (by decide)) (by decide)

/-- Weak Kleene disjunction is not monotone in the truth order either. -/
theorem joinWeak_not_truthMono :
    ¬ ∀ a a' b : Trivalent, a ≤ a' → joinWeak a b ≤ joinWeak a' b :=
  fun h ↦ absurd (h .false .undefined .true (by decide)) (by decide)

/-- Over a nonempty family, the supervaluation of a property is the meet, in the knowledge order, of
the classical truth values the property has at the members. -/
theorem toKnow_supervaluation {α : Type*} {s : Finset α} (P : α → Prop) [DecidablePred P]
    (hs : s.Nonempty) :
    toKnow (supervaluation s P) = s.inf' hs fun a ↦ toKnow (ofProp (P a)) := by
  cases h : supervaluation s P
  · have := ((supervaluation_eq_false_iff ..).1 h).2
    rw [Finset.inf'_congr hs rfl fun a ha ↦ by rw [ofProp_congr (iff_false_intro (this a ha)),
      ofProp_false], Finset.inf'_const]
  · obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (supervaluation_eq_undefined_iff ..).1 h
    refine (le_bot_iff.1 ?_).symm
    calc s.inf' hs (fun a ↦ toKnow (ofProp (P a)))
        ≤ toKnow (ofProp (P a)) ⊓ toKnow (ofProp (P b)) :=
          le_inf (Finset.inf'_le _ ha) (Finset.inf'_le _ hb)
      _ = ⊥ := by rw [ofProp_congr (iff_true_intro hp), ofProp_congr (iff_false_intro hn)]; rfl
  · have := (supervaluation_eq_true_iff ..).1 h
    rw [Finset.inf'_congr hs rfl fun a ha ↦ by rw [ofProp_congr (iff_true_intro (this a ha)),
      ofProp_true], Finset.inf'_const]

/-- Shrinking a family to a nonempty subfamily can only add information to a supervaluation. The
subfamily must be nonempty, since the empty family counts as true by convention, and a larger family
none of whose members has the property is false. -/
theorem supervaluation_kLE_supervaluation {α : Type*} {s t : Finset α} (P : α → Prop)
    [DecidablePred P] (h : s ⊆ t) (hs : s.Nonempty) :
    supervaluation t P ≤ₖ supervaluation s P := by
  rw [kLE_def, toKnow_supervaluation P hs, toKnow_supervaluation P (hs.mono h)]
  exact Finset.inf'_mono _ h hs

end Trivalent
