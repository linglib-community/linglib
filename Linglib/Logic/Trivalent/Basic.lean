/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Core.Order.DeMorganAlgebra.Basic

/-!
# Three-valued truth

`Trivalent` is Kleene's three truth values, ordered by truth: `false < undefined < true`. The
order's meet and join are Strong Kleene conjunction and disjunction, and Kleene negation `ᶜ`
exchanges truth and falsity, so `Trivalent` is a Kleene algebra that is not Boolean. A value is
fixed by whether it is undefined and whether it is true
(`eq_of_eq_undefined_iff_of_eq_true_iff`). The two-valued fragment is the image of `ofProp`, and
Bochvar's assertion operator `ofProp (a = .true)` is conjunction with definedness
(`ofProp_ne_undefined_inf_self`). A `Designation` is one of the standards K3 and LP, named by its
least designated value, and negation exchanges the two (`Designation.dual_threshold_le_compl_iff`).

## Implementation notes

The type follows mathlib's `SignType`: an inductive order relation closed by `decide`, and no
numeric instances. Operations that are expressions in the order get no definition: Strong Kleene
conjunction, disjunction and negation are `⊓`, `⊔` and `ᶜ`, Bochvar's assertion operator is
`ofProp (a = .true)`, Beaver's presupposition operator is `a ⊔ .undefined`, designation at a
standard `d` is `d.threshold ≤ a`, and a Boolean `b` has value `ofProp b`. The constructors
share their names with `Bool`'s, so they are written with dot notation.

## References

* [kleene-1952]
* [bochvar-1938]
* [priest-1979]
* [cobreros-etal-2012]
* [kalman-1958]
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false in
-- Don't generate unnecessary `sizeOf_spec` lemmas which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- Kleene's three truth values. -/
inductive Trivalent
  | false
  | undefined
  | true
  deriving DecidableEq, Inhabited, Fintype, Repr

namespace Trivalent

/-! ### The truth order -/

/-- The truth order, `false < undefined < true`. -/
protected inductive LE : Trivalent → Trivalent → Prop
  | of_false (a) : Trivalent.LE .false a
  | undefined : Trivalent.LE .undefined .undefined
  | of_true (a) : Trivalent.LE a .true

instance : LE Trivalent :=
  ⟨Trivalent.LE⟩

instance : DecidableLE Trivalent := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor!) | exact isFalse (by rintro ⟨_⟩)

instance : LinearOrder Trivalent where
  le_refl a := by cases a <;> constructor
  le_total := by decide
  le_antisymm := by decide
  le_trans := by decide
  toDecidableLE := instDecidableLE

instance : BoundedOrder Trivalent where
  top := .true
  le_top := LE.of_true
  bot := .false
  bot_le := by exact LE.of_false

theorem trichotomy (a : Trivalent) : a = .false ∨ a = .undefined ∨ a = .true := by
  cases a <;> simp

@[simp] theorem top_eq_true : (⊤ : Trivalent) = .true := rfl
@[simp] theorem bot_eq_false : (⊥ : Trivalent) = .false := rfl

@[simp] theorem le_true (a : Trivalent) : a ≤ .true := LE.of_true a
@[simp] theorem false_le (a : Trivalent) : .false ≤ a := LE.of_false a

@[simp] theorem true_le_iff {a : Trivalent} : .true ≤ a ↔ a = .true := top_le_iff
@[simp] theorem le_false_iff {a : Trivalent} : a ≤ .false ↔ a = .false := le_bot_iff

/-- Two values agree once they agree on being undefined and on being true. -/
theorem eq_of_eq_undefined_iff_of_eq_true_iff {a b : Trivalent}
    (h₀ : a = .undefined ↔ b = .undefined)
    (h₁ : a = .true ↔ b = .true) : a = b := by
  revert h₀ h₁; cases a <;> cases b <;> decide

/-- Two values agree once they agree on being true and on being false. -/
theorem eq_of_eq_true_iff_of_eq_false_iff {a b : Trivalent} (h₁ : a = .true ↔ b = .true)
    (h₂ : a = .false ↔ b = .false) : a = b := by
  revert h₁ h₂; cases a <;> cases b <;> decide

@[simp] theorem le_undefined_iff_ne_true {a : Trivalent} : a ≤ .undefined ↔ a ≠ .true := by
  cases a <;> decide

@[simp] theorem undefined_le_iff_ne_false {a : Trivalent} : .undefined ≤ a ↔ a ≠ .false := by
  cases a <;> decide

theorem eq_undefined_iff {a : Trivalent} : a = .undefined ↔ a ≠ .true ∧ a ≠ .false := by
  rw [le_antisymm_iff, le_undefined_iff_ne_true, undefined_le_iff_ne_false]

theorem sup_true (a : Trivalent) : a ⊔ .true = .true := by cases a <;> rfl
theorem true_sup (a : Trivalent) : .true ⊔ a = .true := by cases a <;> rfl
theorem inf_false (a : Trivalent) : a ⊓ .false = .false := by cases a <;> rfl
theorem false_inf (a : Trivalent) : .false ⊓ a = .false := by cases a <;> rfl
theorem inf_true (a : Trivalent) : a ⊓ .true = a := by cases a <;> rfl
theorem true_inf (a : Trivalent) : .true ⊓ a = a := by cases a <;> rfl
theorem sup_false (a : Trivalent) : a ⊔ .false = a := by cases a <;> rfl
theorem false_sup (a : Trivalent) : .false ⊔ a = a := by cases a <;> rfl

@[simp] theorem inf_eq_true_iff {a b : Trivalent} : a ⊓ b = .true ↔ a = .true ∧ b = .true := by
  cases a <;> cases b <;> decide

@[simp] theorem sup_eq_false_iff {a b : Trivalent} :
    a ⊔ b = .false ↔ a = .false ∧ b = .false := by
  cases a <;> cases b <;> decide

@[simp] theorem sup_eq_true_iff {a b : Trivalent} : a ⊔ b = .true ↔ a = .true ∨ b = .true := by
  cases a <;> cases b <;> decide

@[simp] theorem inf_eq_false_iff {a b : Trivalent} :
    a ⊓ b = .false ↔ a = .false ∨ b = .false := by
  cases a <;> cases b <;> decide

@[simp] theorem inf_eq_undefined_iff {a b : Trivalent} :
    a ⊓ b = .undefined ↔ a = .undefined ∧ b ≠ .false ∨ b = .undefined ∧ a ≠ .false := by
  cases a <;> cases b <;> decide

@[simp] theorem sup_eq_undefined_iff {a b : Trivalent} :
    a ⊔ b = .undefined ↔ a = .undefined ∧ b ≠ .true ∨ b = .undefined ∧ a ≠ .true := by
  cases a <;> cases b <;> decide

/-! ### Kleene's negation -/

/-- Kleene negation exchanges truth and falsity and fixes `undefined`. -/
instance : InvolutiveCompl Trivalent where
  compl
    | .false => .true
    | .undefined => .undefined
    | .true => .false
  compl_compl a := by cases a <;> rfl
  compl_le_compl {a b} := by cases a <;> cases b <;> decide

@[simp] theorem compl_false : Trivalent.falseᶜ = .true := rfl
@[simp] theorem compl_undefined : Trivalent.undefinedᶜ = .undefined := rfl
@[simp] theorem compl_true : Trivalent.trueᶜ = .false := rfl

@[simp] theorem compl_eq_true_iff {a : Trivalent} : aᶜ = .true ↔ a = .false := by
  cases a <;> decide

@[simp] theorem compl_eq_false_iff {a : Trivalent} : aᶜ = .false ↔ a = .true := by
  cases a <;> decide

@[simp] theorem compl_eq_undefined_iff {a : Trivalent} : aᶜ = .undefined ↔ a = .undefined := by
  cases a <;> decide

@[simp] theorem compl_compl (a : Trivalent) : aᶜᶜ = a := InvolutiveCompl.compl_compl a

theorem compl_antitone : Antitone (compl : Trivalent → Trivalent) :=
  fun _ _ ↦ InvolutiveCompl.compl_le_compl

theorem compl_inf (a b : Trivalent) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := compl_antitone.map_min

theorem compl_sup (a b : Trivalent) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := compl_antitone.map_max

/-- `Trivalent` is [kalman-1958]'s three-element Kleene algebra. -/
instance : IsKleene Trivalent := ⟨by decide⟩

theorem inf_compl_undefined_ne_bot : Trivalent.undefined ⊓ Trivalent.undefinedᶜ ≠ ⊥ := by decide

/-! ### The two-valued fragment -/

/-- The value of a decidable proposition is `true` or `false`. -/
def ofProp (P : Prop) [Decidable P] : Trivalent := if P then .true else .false

section OfProp

variable {P Q : Prop} [Decidable P] [Decidable Q]

@[simp] theorem ofProp_eq_true_iff : ofProp P = .true ↔ P := by
  by_cases h : P <;> simp [ofProp, h]

@[simp] theorem ofProp_eq_false_iff : ofProp P = .false ↔ ¬ P := by
  by_cases h : P <;> simp [ofProp, h]

@[simp] theorem ofProp_ne_undefined : ofProp P ≠ .undefined := by
  by_cases h : P <;> simp [ofProp, h]

theorem undefined_le_ofProp_iff : .undefined ≤ ofProp P ↔ P := by
  by_cases h : P <;> simp [ofProp, h]

theorem ofProp_eq_true_of_ne_undefined {a : Trivalent} [Decidable (a = .true)]
    (h : a ≠ .undefined) : ofProp (a = .true) = a := by
  revert h; cases a <;> simp

/-- Bochvar's assertion operator is Strong Kleene conjunction with definedness. -/
theorem ofProp_ne_undefined_inf_self (a : Trivalent) :
    ofProp (a ≠ .undefined) ⊓ a = ofProp (a = .true) := by
  cases a <;> decide

@[congr] theorem ofProp_congr (h : P ↔ Q) : ofProp P = ofProp Q :=
  eq_of_eq_undefined_iff_of_eq_true_iff (by simp) (by simp [h])

@[simp] theorem ofProp_true [Decidable True] : ofProp True = .true := by simp [ofProp]

@[simp] theorem ofProp_false [Decidable False] : ofProp False = .false := by simp [ofProp]

@[simp] theorem ofProp_and : ofProp (P ∧ Q) = ofProp P ⊓ ofProp Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [ofProp, hP, hQ]

@[simp] theorem ofProp_or : ofProp (P ∨ Q) = ofProp P ⊔ ofProp Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [ofProp, hP, hQ]

@[simp] theorem ofProp_not : ofProp (¬ P) = (ofProp P)ᶜ := by
  by_cases h : P <;> simp [ofProp, h]

end OfProp

/-! ### Designated values

Matrix semantics fixes an upward-closed set of *designated* values; on a chain every such set is
principal, so a designation standard is just a threshold, and a value `v` is designated at `d`
when `d.threshold ≤ v`. K3, Strong Kleene logic, designates `{true}` and preserves truth; LP,
[priest-1979]'s Logic of Paradox, designates `{undefined, true}` and preserves non-falsity. The
two standards give dual logics over one algebra ([cobreros-etal-2012]), and every law of
designation is a law of the order. -/

/-- A designation standard, identified by its least designated value (`threshold`). -/
inductive Designation where
  | k3
  | lp
  deriving Repr, DecidableEq, Inhabited, Fintype

/-- The least designated value of a standard. -/
def Designation.threshold : Designation → Trivalent
  | .k3 => .true
  | .lp => .undefined

/-- The K3/LP duality as an involution on standards. -/
def Designation.dual : Designation → Designation
  | .k3 => .lp
  | .lp => .k3

@[simp] theorem Designation.dual_dual (d : Designation) : d.dual.dual = d := by
  cases d <;> rfl

@[simp] theorem Designation.dual_k3 : Designation.k3.dual = .lp := rfl
@[simp] theorem Designation.dual_lp : Designation.lp.dual = .k3 := rfl

@[simp] theorem Designation.threshold_k3 : Designation.k3.threshold = .true := rfl
@[simp] theorem Designation.threshold_lp : Designation.lp.threshold = .undefined := rfl

/-- Negation swaps the designation standards, fixing `undefined` and exchanging the complements of
the two principal filters. -/
theorem Designation.dual_threshold_le_compl_iff (d : Designation) (v : Trivalent) :
    d.dual.threshold ≤ vᶜ ↔ ¬ d.threshold ≤ v := by
  cases d <;> cases v <;> decide

theorem Designation.threshold_le_ofProp_iff (d : Designation) (P : Prop) [Decidable P] :
    d.threshold ≤ ofProp P ↔ P := by
  cases d <;> by_cases h : P <;> simp only [ofProp, h, ite_true, ite_false, iff_true, iff_false] <;>
    decide

end Trivalent
