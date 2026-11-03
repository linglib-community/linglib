/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Linglib.Logic.Trivalent.Basic
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Fintype.Powerset

/-!
# Three-valued truth as sets of classical values

A three-valued truth value can be read as the set of classical values it leaves open: `1` is
`{true}`, `-1` is `{false}` and the undefined `0` is `{true, false}`. Lifting a Boolean operation
pointwise to these sets computes every classical result compatible with its inputs, and for
negation, conjunction, disjunction and the biconditional the lift is Kleene's strong table. This is
the reading behind Kleene's regularity ([kleene-1952]). The Weak Kleene connectives are no such
lift.

The lift is compositional: a formula's value is computed connective by connective, so an undefined
`p` leaves `p ∧ ¬p` undefined. Lifting the whole formula as one Boolean function instead keeps
track of which occurrences share a value, and gives the supervaluation of [van-fraassen-1966],
which makes `p ∧ ¬p` false.

## Main definitions

* `SignType.toFinset`, `SignType.ofFinset`, `SignType.equivNonemptyFinset`: a value as the
  nonempty set of classical values it leaves open.

## Main results

* `SignType.toFinset_neg`, `SignType.toFinset_inf`, `SignType.toFinset_sup`,
  `SignType.toFinset_mul`: the Strong Kleene connectives are the pointwise lifts of `!`, `&&`,
  `||` and `==`.
* `SignType.toFinset_meetWeak_ne`: Weak Kleene conjunction is not the lift of `&&`.
* `SignType.toFinset_supervaluation`: over a nonempty family, the supervaluation is the set of
  classical values, the lift of a whole formula.
* `SignType.toFinset_inf_neg_self_ne`: lifting connective by connective and lifting the formula
  differ on `p ∧ ¬p`.

## References

* [kleene-1952]
* [van-fraassen-1966]
-/

@[expose] public section

namespace SignType

/-- The classical values a value leaves open: `{true}`, `{false}`, or both when undefined. -/
def toFinset : SignType → Finset Bool
  | .pos => {true}
  | .neg => {false}
  | .zero => {true, false}

theorem toFinset_nonempty (a : SignType) : (toFinset a).Nonempty := by
  cases a <;> decide

theorem toFinset_injective : Function.Injective toFinset := by
  intro a b; cases a <;> cases b <;> decide

/-- The value leaving open the classical values of a nonempty set. -/
def ofFinset (s : Finset Bool) : SignType :=
  if s = {true} then 1 else if s = {false} then -1 else 0

theorem ofFinset_toFinset (a : SignType) : ofFinset (toFinset a) = a := by
  cases a <;> decide

theorem toFinset_ofFinset {s : Finset Bool} (hs : s.Nonempty) : toFinset (ofFinset s) = s := by
  revert s; decide

/-- `SignType` is the nonempty sets of classical values. -/
def equivNonemptyFinset : SignType ≃ {s : Finset Bool // s.Nonempty} where
  toFun a := ⟨toFinset a, toFinset_nonempty a⟩
  invFun s := ofFinset s
  left_inv := ofFinset_toFinset
  right_inv s := Subtype.ext (toFinset_ofFinset s.2)

/-! ### The Strong Kleene connectives are pointwise lifts -/

/-- Strong Kleene negation is the lift of `!`. -/
theorem toFinset_neg (a : SignType) : toFinset (-a) = (toFinset a).image (!·) := by
  cases a <;> decide

/-- Strong Kleene conjunction is the lift of `&&`. -/
theorem toFinset_inf (a b : SignType) :
    toFinset (a ⊓ b) = Finset.image₂ (· && ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- Strong Kleene disjunction is the lift of `||`. -/
theorem toFinset_sup (a b : SignType) :
    toFinset (a ⊔ b) = Finset.image₂ (· || ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- The Strong Kleene biconditional, multiplication, is the lift of `==`. -/
theorem toFinset_mul (a b : SignType) :
    toFinset (a * b) = Finset.image₂ (· == ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- Weak Kleene conjunction is not the lift of `&&`, since a false conjunct settles the lift but
not `meetWeak 0 (-1) = 0`. -/
theorem toFinset_meetWeak_ne :
    toFinset (meetWeak 0 (-1)) ≠ Finset.image₂ (· && ·) (toFinset 0) (toFinset (-1)) := by
  decide

/-! ### Lifting a whole formula -/

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

/-- At an undefined `p`, lifting conjunction and negation separately leaves `p ∧ ¬p` undefined,
while lifting `fun x ↦ x && !x` as a whole makes it false. -/
theorem toFinset_inf_neg_self_ne :
    toFinset (0 ⊓ -0) ≠ (toFinset 0).image (fun x ↦ x && !x) := by
  decide

end SignType
