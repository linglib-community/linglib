/-
Copyright (c) 2026 Patrick Elliott. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Elliott
-/
module

public import Linglib.Logic.Trivalent.Knowledge
public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Fintype.Powerset

/-!
# Three-valued truth as sets of classical values

A three-valued truth value can be read as the set of classical values it leaves open: `true` is
`{true}`, `false` is `{false}` and `undefined` is `{true, false}`. These are the values of its
two bivalent readings, its designation at K3 and at LP, so the set of a value is the
supervaluation reading of `Linglib.Logic.Trivalent.Supervaluation` at a single occurrence.

Lifting a Boolean operation pointwise to these sets computes every classical result compatible
with its inputs, and for negation, conjunction, disjunction and the biconditional the lift is
Kleene's strong table; `Trivalent.Formula.eval_strongKleene_eq_supervaluation` extends this to
whole formulas. The Weak Kleene connectives are the lift of no Boolean operation. The knowledge
order of `Linglib.Logic.Trivalent.Knowledge` is reverse inclusion, so a lifted operation is monotone
for it, which is Kleene's regularity ([kleene-1952]).

## Main definitions

* `Trivalent.toFinset`, `Trivalent.ofFinset`, `Trivalent.equivNonemptyFinsetBool`: a value as the
  nonempty set of classical values it leaves open.

## Main results

* `Trivalent.toFinset_eq_image_threshold_le`: the set of a value is the set of its designations at
  the two standards.
* `Trivalent.toFinset_supervaluation`: over a nonempty family, the supervaluation is the set of
  classical values ([van-fraassen-1966]).
* `Trivalent.toFinset_compl`, `Trivalent.toFinset_inf`, `Trivalent.toFinset_sup`,
  `Trivalent.toFinset_compl_sup_inf_sup_compl`: the Strong Kleene connectives are the pointwise
  lifts of `!`, `&&`, `||` and `==`.
* `Trivalent.meetWeak_not_lift`, `Trivalent.joinWeak_not_lift`: the Weak Kleene connectives are the
  lift of no Boolean operation.
* `Trivalent.kLE_iff_toFinset_subset`: the knowledge order is reverse inclusion.

## References

* [kleene-1952]
* [van-fraassen-1966]
-/

@[expose] public section

namespace Trivalent

open Bilattice

/-! ### Values as sets of classical values -/

/-- The classical values a value leaves open: `{true}`, `{false}`, or both when undefined. -/
def toFinset : Trivalent → Finset Bool
  | .true => {Bool.true}
  | .false => {Bool.false}
  | .undefined => {Bool.true, Bool.false}

@[simp] theorem toFinset_true : toFinset .true = {Bool.true} := rfl

@[simp] theorem toFinset_false : toFinset .false = {Bool.false} := rfl

@[simp] theorem toFinset_undefined : toFinset .undefined = {Bool.true, Bool.false} := rfl

theorem toFinset_nonempty (a : Trivalent) : (toFinset a).Nonempty := by
  cases a <;> decide

theorem toFinset_injective : Function.Injective toFinset := by
  intro a b; cases a <;> cases b <;> decide

@[simp] theorem toFinset_inj {a b : Trivalent} : toFinset a = toFinset b ↔ a = b :=
  toFinset_injective.eq_iff

/-- The value leaving open the classical values of a set, sending the empty set, which no value
leaves open, to `undefined`. -/
def ofFinset (s : Finset Bool) : Trivalent :=
  if s = {Bool.true} then .true else if s = {Bool.false} then .false else .undefined

theorem ofFinset_toFinset (a : Trivalent) : ofFinset (toFinset a) = a := by
  cases a <;> decide

theorem toFinset_ofFinset {s : Finset Bool} (hs : s.Nonempty) : toFinset (ofFinset s) = s := by
  revert s; decide

/-- The values are the nonempty sets of classical values. -/
def equivNonemptyFinsetBool : Trivalent ≃ {s : Finset Bool // s.Nonempty} where
  toFun a := ⟨toFinset a, toFinset_nonempty a⟩
  invFun s := ofFinset s
  left_inv := ofFinset_toFinset
  right_inv s := Subtype.ext (toFinset_ofFinset s.2)

/-- The set of a value is the set of its two bivalent readings, its designations at K3 and LP. -/
theorem toFinset_eq_image_threshold_le (a : Trivalent) :
    toFinset a = Finset.univ.image fun d : Trivalent.Designation ↦ decide (d.threshold ≤ a) := by
  cases a <;> decide

/-- Over a nonempty family, the supervaluation of `P` leaves open exactly the classical values `P`
takes on the family. -/
theorem toFinset_supervaluation {α : Type*} {s : Finset α} (P : α → Prop) [DecidablePred P]
    (hs : s.Nonempty) : toFinset (supervaluation s P) = s.image fun a ↦ decide (P a) := by
  cases h : supervaluation s P
  · have := ((supervaluation_eq_false_iff ..).1 h).2
    rw [Finset.image_congr fun a ha ↦ decide_eq_false (this a ha), Finset.image_const hs]
    rfl
  · obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (supervaluation_eq_undefined_iff ..).1 h
    ext x
    cases x
    · exact iff_of_true (by decide) (Finset.mem_image.2 ⟨b, hb, decide_eq_false hn⟩)
    · exact iff_of_true (by decide) (Finset.mem_image.2 ⟨a, ha, decide_eq_true hp⟩)
  · have := (supervaluation_eq_true_iff ..).1 h
    rw [Finset.image_congr fun a ha ↦ decide_eq_true (this a ha), Finset.image_const hs]
    rfl

/-! ### Connectives as pointwise lifts -/

/-- Kleene negation is the lift of `!`. -/
@[simp] theorem toFinset_compl (a : Trivalent) : toFinset aᶜ = (toFinset a).image (!·) := by
  cases a <;> decide

/-- Strong Kleene conjunction is the lift of `&&`. -/
@[simp] theorem toFinset_inf (a b : Trivalent) :
    toFinset (a ⊓ b) = Finset.image₂ (· && ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- Strong Kleene disjunction is the lift of `||`. -/
@[simp] theorem toFinset_sup (a b : Trivalent) :
    toFinset (a ⊔ b) = Finset.image₂ (· || ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- The Strong Kleene biconditional `(¬a ∨ b) ∧ (a ∨ ¬b)` is the lift of `==`. -/
@[simp] theorem toFinset_compl_sup_inf_sup_compl (a b : Trivalent) :
    toFinset ((aᶜ ⊔ b) ⊓ (a ⊔ bᶜ)) = Finset.image₂ (· == ·) (toFinset a) (toFinset b) := by
  cases a <;> cases b <;> decide

/-- Weak Kleene conjunction is the lift of no Boolean operation, since an undefined operand makes
it undefined even where the lift is settled. -/
theorem meetWeak_not_lift : ¬ ∃ f : Bool → Bool → Bool, ∀ a b : Trivalent,
    toFinset (meetWeak a b) = Finset.image₂ f (toFinset a) (toFinset b) := by
  decide

/-- Weak Kleene disjunction is the lift of no Boolean operation. -/
theorem joinWeak_not_lift : ¬ ∃ f : Bool → Bool → Bool, ∀ a b : Trivalent,
    toFinset (joinWeak a b) = Finset.image₂ f (toFinset a) (toFinset b) := by
  decide

/-! ### The knowledge order -/

/-- The knowledge order is reverse inclusion: a value is more informative when it leaves fewer
classical values open. -/
theorem kLE_iff_toFinset_subset {a b : Trivalent} : a ≤ₖ b ↔ toFinset b ⊆ toFinset a := by
  rw [kLE_iff]; cases a <;> cases b <;> decide

end Trivalent
