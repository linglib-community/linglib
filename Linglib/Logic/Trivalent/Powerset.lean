/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Linglib.Logic.Trivalent.Flat
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Fintype.Powerset

/-!
# Three-valued truth as sets of classical values

A three-valued truth value can be read as the set of classical values it leaves open: `1` is
`{true}`, `-1` is `{false}` and the undefined `0` is `{true, false}`. These are the values of its
two bivalent readings, its designation at K3 and at LP, so the set of a value is the
supervaluation reading of `Linglib.Logic.Trivalent.Supervaluation` at a single occurrence.

Lifting a Boolean operation pointwise to these sets computes every classical result compatible
with its inputs, and for negation, conjunction, disjunction and the biconditional the lift is
Kleene's strong table; `Trivalent.Formula.eval_strongKleene_eq_supervaluation` extends this to
whole formulas. The Weak Kleene connectives are the lift of no Boolean operation. The knowledge
order of `Linglib.Logic.Trivalent.Flat` is reverse inclusion, so a lifted operation is monotone
for it, which is Kleene's regularity ([kleene-1952]).

## Main definitions

* `SignType.toFinset`, `SignType.ofFinset`, `SignType.equivNonemptyFinsetBool`: a value as the
  nonempty set of classical values it leaves open.

## Main results

* `SignType.toFinset_eq_image_threshold_le`: the set of a value is the set of its designations at
  the two standards.
* `SignType.toFinset_supervaluation`: over a nonempty family, the supervaluation is the set of
  classical values ([van-fraassen-1966]).
* `SignType.toFinset_neg`, `SignType.toFinset_inf`, `SignType.toFinset_sup`,
  `SignType.toFinset_mul`: the Strong Kleene connectives are the pointwise lifts of `!`, `&&`,
  `||` and `==`.
* `SignType.meetWeak_not_lift`, `SignType.joinWeak_not_lift`: the Weak Kleene connectives are the
  lift of no Boolean operation.
* `SignType.toFlat_le_toFlat_iff_toFinset_subset`: the knowledge order is reverse inclusion.

## References

* [kleene-1952]
* [van-fraassen-1966]
-/

@[expose] public section

namespace SignType

/-! ### Values as sets of classical values -/

/-- The classical values a value leaves open: `{true}`, `{false}`, or both when undefined. -/
def toFinset : SignType → Finset Bool
  | .pos => {true}
  | .neg => {false}
  | .zero => {true, false}

@[simp] theorem toFinset_one : toFinset 1 = {true} := rfl

@[simp] theorem toFinset_neg_one : toFinset (-1) = {false} := rfl

@[simp] theorem toFinset_zero : toFinset 0 = {true, false} := rfl

theorem toFinset_nonempty (a : SignType) : (toFinset a).Nonempty := by
  cases a <;> decide

theorem toFinset_injective : Function.Injective toFinset := by
  intro a b; cases a <;> cases b <;> decide

@[simp] theorem toFinset_inj {a b : SignType} : toFinset a = toFinset b ↔ a = b :=
  toFinset_injective.eq_iff

/-- The value leaving open the classical values of a set, sending the empty set, which no value
leaves open, to `0`. -/
def ofFinset (s : Finset Bool) : SignType :=
  if s = {true} then 1 else if s = {false} then -1 else 0

theorem ofFinset_toFinset (a : SignType) : ofFinset (toFinset a) = a := by
  cases a <;> decide

theorem toFinset_ofFinset {s : Finset Bool} (hs : s.Nonempty) : toFinset (ofFinset s) = s := by
  revert s; decide

/-- The values are the nonempty sets of classical values. -/
def equivNonemptyFinsetBool : SignType ≃ {s : Finset Bool // s.Nonempty} where
  toFun a := ⟨toFinset a, toFinset_nonempty a⟩
  invFun s := ofFinset s
  left_inv := ofFinset_toFinset
  right_inv s := Subtype.ext (toFinset_ofFinset s.2)

/-- The set of a value is the set of its two bivalent readings, its designations at K3 and LP. -/
theorem toFinset_eq_image_threshold_le (a : SignType) :
    toFinset a = Finset.univ.image fun d : Trivalent.Designation ↦ decide (d.threshold ≤ a) := by
  cases a <;> decide

/-- Over a nonempty family, the supervaluation of `P` leaves open exactly the classical values `P`
takes on the family. -/
theorem toFinset_supervaluation {α : Type*} {s : Finset α} (P : α → Prop) [DecidablePred P]
    (hs : s.Nonempty) : toFinset (supervaluation s P) = s.image fun a ↦ decide (P a) := by
  cases h : supervaluation s P
  · obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (supervaluation_eq_zero_iff ..).1 h
    ext x
    cases x
    · exact iff_of_true (by decide) (Finset.mem_image.2 ⟨b, hb, decide_eq_false hn⟩)
    · exact iff_of_true (by decide) (Finset.mem_image.2 ⟨a, ha, decide_eq_true hp⟩)
  · have := ((supervaluation_eq_neg_one_iff ..).1 h).2
    rw [Finset.image_congr fun a ha ↦ decide_eq_false (this a ha), Finset.image_const hs]
    rfl
  · have := (supervaluation_eq_one_iff ..).1 h
    rw [Finset.image_congr fun a ha ↦ decide_eq_true (this a ha), Finset.image_const hs]
    rfl

/-! ### Connectives as pointwise lifts -/

/-- Strong Kleene negation is the lift of `!`. -/
@[simp] theorem toFinset_neg (a : SignType) : toFinset (-a) = (toFinset a).image (!·) := by
  cases a <;> decide

/-- Strong Kleene conjunction is the lift of `&&`. -/
@[simp] theorem toFinset_inf (a b : SignType) :
    toFinset (a ⊓ b) = Finset.image₂ (· && ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- Strong Kleene disjunction is the lift of `||`. -/
@[simp] theorem toFinset_sup (a b : SignType) :
    toFinset (a ⊔ b) = Finset.image₂ (· || ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- The Strong Kleene biconditional, multiplication, is the lift of `==`. -/
@[simp] theorem toFinset_mul (a b : SignType) :
    toFinset (a * b) = Finset.image₂ (· == ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- Weak Kleene conjunction is the lift of no Boolean operation, since an undefined operand makes
it undefined even where the lift is settled. -/
theorem meetWeak_not_lift : ¬ ∃ f : Bool → Bool → Bool, ∀ a b : SignType,
    toFinset (meetWeak a b) = Finset.image₂ f (toFinset a) (toFinset b) := by
  decide

/-- Weak Kleene disjunction is the lift of no Boolean operation. -/
theorem joinWeak_not_lift : ¬ ∃ f : Bool → Bool → Bool, ∀ a b : SignType,
    toFinset (joinWeak a b) = Finset.image₂ f (toFinset a) (toFinset b) := by
  decide

/-! ### The knowledge order -/

/-- The knowledge order is reverse inclusion: a value is more informative when it leaves fewer
classical values open. -/
theorem toFlat_le_toFlat_iff_toFinset_subset {a b : SignType} :
    toFlat a ≤ toFlat b ↔ toFinset b ⊆ toFinset a := by
  rw [toFlat_le_toFlat_iff]; cases a <;> cases b <;> decide

end SignType
