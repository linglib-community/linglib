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

A sentence can fail to be true without being false. Strawson argued that *The King of France is
bald* has no truth value when there is no king of France, and a semantics of presupposition gives
such a sentence a third value. Kleene's three values are **true**, **false** and **undefined**,
ordered by truth with undefined in the middle. Meet and join are his strong conjunction and
disjunction: one false conjunct makes a conjunction false, and one true disjunct makes a disjunction
true. Negation exchanges true and false and fixes undefined, so *p or not p* is undefined when *p*
is.

Bochvar's assertion operator asks whether a value is true, sending undefined to false. A logic also
has to say which values count as holding: true alone, or undefined as well.

## Implementation notes

The type follows mathlib's `SignType`: an inductive order relation closed by `decide`, and no
numeric instances. Operations that are expressions in the order get no definition: Strong Kleene
conjunction, disjunction and negation are `⊓`, `⊔` and `ᶜ`, Bochvar's assertion operator is `ofProp
(a = .true)`, Beaver's presupposition operator is `a ⊔ .undefined`, designation at a standard `d` is
`d.threshold ≤ a`, and a Boolean `b` has value `ofProp b`. The constructors share their names with
`Bool`'s, so they are written with dot notation.

## References

* [kleene-1952]
* [bochvar-1938]
* [priest-1979]
* [cobreros-etal-2012]
* [kalman-1958]
* [beaver-geurts-denlinger-2021]
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false in
-- Don't generate unnecessary `sizeOf_spec` lemmas which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- A **truth value** is one of Kleene's three: true, false or undefined. -/
inductive Trivalent
  | false
  | undefined
  | true
  deriving DecidableEq, Inhabited, Fintype, Repr

namespace Trivalent

/-!
### The truth order

The values are ordered by how true they are: false, then undefined, then true. The order is a chain
with false at the bottom and true at the top, and its meet and join are Strong Kleene conjunction
and disjunction.
-/

/-- The **truth order** puts false below undefined and undefined below true. -/
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

/-!
### Kleene's negation

Negation reverses the truth order and undoes itself, so the De Morgan laws hold. It is not a Boolean
complement: undefined is its own negation, and *p and not p* is then undefined, not false.
-/

/-- **Kleene negation** exchanges true and false and leaves undefined as it is. -/
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

/-- The conjunction of a value with its negation is never above the disjunction of another value
with its negation. In words, a contradiction is never truer than an instance of excluded middle. -/
instance : IsKleene Trivalent := ⟨by decide⟩

theorem inf_compl_undefined_ne_bot : Trivalent.undefined ⊓ Trivalent.undefinedᶜ ≠ ⊥ := by decide

/-!
### The two-valued fragment

A proposition that simply holds or fails has the value true or false, and on such values
conjunction, disjunction and negation are the classical ones. Bochvar's assertion operator maps
every value into this fragment.
-/

/-- The **value** of a two-valued proposition is true if the proposition holds and false if it does
not. -/
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

/-- Conjoining a value with the two-valued statement that it is defined gives true if the value is
true and false otherwise, which is Bochvar's assertion of the value. -/
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

/-!
### Designated values

A logic over the three values fixes which of them are **designated**, the values that count as
holding. They are the values at or above a threshold. Strong Kleene logic, K3, designates true alone
and preserves truth. Priest's Logic of Paradox, LP, designates undefined as well and preserves
non-falsity. Cobreros and coauthors treat the two as dual logics over one algebra.
-/

/-- A **designation standard** says which truth values count as holding. There are two, K3 and
LP. -/
inductive Designation where
  | k3
  | lp
  deriving Repr, DecidableEq, Inhabited, Fintype

/-- The **threshold** of a standard is its least designated value: true for K3, undefined for LP. -/
def Designation.threshold : Designation → Trivalent
  | .k3 => .true
  | .lp => .undefined

/-- The **dual** of a standard is the other one. -/
def Designation.dual : Designation → Designation
  | .k3 => .lp
  | .lp => .k3

@[simp] theorem Designation.dual_dual (d : Designation) : d.dual.dual = d := by
  cases d <;> rfl

@[simp] theorem Designation.dual_k3 : Designation.k3.dual = .lp := rfl
@[simp] theorem Designation.dual_lp : Designation.lp.dual = .k3 := rfl

@[simp] theorem Designation.threshold_k3 : Designation.k3.threshold = .true := rfl
@[simp] theorem Designation.threshold_lp : Designation.lp.threshold = .undefined := rfl

/-- A negation is designated at the dual standard exactly when the value negated is not designated
at the standard. -/
theorem Designation.dual_threshold_le_compl_iff (d : Designation) (v : Trivalent) :
    d.dual.threshold ≤ vᶜ ↔ ¬ d.threshold ≤ v := by
  cases d <;> cases v <;> decide

theorem Designation.threshold_le_ofProp_iff (d : Designation) (P : Prop) [Decidable P] :
    d.threshold ≤ ofProp P ↔ P := by
  cases d <;> by_cases h : P <;> simp only [ofProp, h, ite_true, ite_false, iff_true, iff_false] <;>
    decide

end Trivalent
