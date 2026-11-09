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
exchanges truth and falsity, so `Trivalent` is a Kleene algebra that is not Boolean. The other
three-valued conjunctions and disjunctions differ from Kleene's only in when a compound is
undefined.

## Main definitions

* `Trivalent`: the three values, with the truth order and Kleene negation.
* `Trivalent.Designation`: the K3 and LP standards, each named by its least designated value.
* `Trivalent.ofProp`: the two-valued fragment.
* `Trivalent.meetWith`, `Trivalent.joinWith`: the conjunction and disjunction undefined exactly
  where a given condition fails.
* `Trivalent.meetWeak`, `Trivalent.meetMiddle`, `Trivalent.meetBelnap` and their joins: the Weak
  Kleene, Middle Kleene and Belnap connectives.
* `Trivalent.transplication`: the binary presupposition operator of [blamey-1986].
* `Trivalent.condAssert`: conditional assertion at a designation standard, de Finetti's
  conditional at K3 and Cooper's at LP.
* `Trivalent.supervaluation`: the value of a predicate over a finite family of valuations.
* `Trivalent.Connectives`: an interpretation of the binary connectives by truth tables, with the
  Strong, Weak and Middle Kleene, Cooper and de Finetti instances.

## Main results

* `Trivalent.eq_of_eq_undefined_iff_of_eq_true_iff`: a value is fixed by whether it is undefined
  and whether it is true.
* `Trivalent.ofProp_ne_undefined_inf_self`: Bochvar's assertion operator is conjunction with
  definedness.
* `Trivalent.Designation.dual_threshold_le_compl_iff`: negation exchanges the K3 and LP standards.
* `Trivalent.meetWeak_eq_meetWith` and companions: each connective is `meetWith` or `joinWith` at
  its definedness condition.
* `Trivalent.transplication_self`, `Trivalent.transplication_eq`: Beaver's presupposition
  operator is the diagonal of transplication, and transplication is definable from it.
* `Trivalent.condAssert_k3`: de Finetti's conditional is transplication.
* `Trivalent.compl_condAssert`, `Trivalent.condAssert_condAssert`: conditional assertion commutes
  with negation and satisfies Import-Export.

## Implementation notes

The type follows mathlib's `SignType`: an inductive order relation closed by `decide`, and no
numeric instances. Operations that are expressions in the order get no definition: Strong Kleene
conjunction, disjunction and negation are `⊓`, `⊔` and `ᶜ`, Bochvar's assertion operator is
`ofProp (a = .true)`, Beaver's presupposition operator is `a ⊔ .undefined`, designation at a
standard `d` is `d.threshold ≤ a`, and a Boolean `b` has value `ofProp b`. Every other connective
keeps a pattern-matched definition, so that `rfl` and `decide` evaluate it. The constructors
share their names with `Bool`'s, so they are written with dot notation and the namespace is
opened selectively.

## References

* [kleene-1952]
* [bochvar-1938]
* [peters-1979]
* [belnap-1970]
* [de-finetti-1936]
* [cooper-1968]
* [priest-1979]
* [cobreros-etal-2012]
* [kalman-1958]
* [beaver-1992]
* [beaver-krahmer-2001]
* [blamey-1986]
* [van-fraassen-1966]
* [george-2014]
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

/-! ### Definedness conditions

The binary conjunctions share one truth rule, false when either operand is and true otherwise,
and differ only in where they are undefined. Strong Kleene conjunction is defined whenever the
operands settle the value, Weak Kleene's demands both operands defined, Belnap's demands one, and
Middle Kleene's is defined when the left operand is and either settles the value or the right
operand is defined too. `meetWith` makes the conjunction a function of that condition. -/

/-- The conjunction undefined unless `D` holds, and otherwise false exactly when an operand is. -/
def meetWith (D : Prop) [Decidable D] (a b : Trivalent) : Trivalent :=
  if D then if a = .false ∨ b = .false then .false else .true else .undefined

/-- The disjunction undefined unless `D` holds, the dual of `meetWith`. -/
def joinWith (D : Prop) [Decidable D] (a b : Trivalent) : Trivalent :=
  (meetWith D aᶜ bᶜ)ᶜ

section DefinednessConditions

variable {D : Prop} [Decidable D] {a b : Trivalent}

theorem meetWith_eq_undefined_iff : meetWith D a b = .undefined ↔ ¬D := by
  by_cases hD : D <;> by_cases h : a = .false ∨ b = .false <;> simp [meetWith, hD, h]

theorem meetWith_eq_false_iff : meetWith D a b = .false ↔ D ∧ (a = .false ∨ b = .false) := by
  by_cases hD : D <;> by_cases h : a = .false ∨ b = .false <;> simp [meetWith, hD, h]

theorem meetWith_eq_true_iff : meetWith D a b = .true ↔ D ∧ a ≠ .false ∧ b ≠ .false := by
  rw [show (a ≠ .false ∧ b ≠ .false) ↔ ¬(a = .false ∨ b = .false) from not_or.symm]
  by_cases hD : D <;> by_cases h : a = .false ∨ b = .false <;> simp [meetWith, hD, h]

theorem joinWith_eq_undefined_iff : joinWith D a b = .undefined ↔ ¬D := by
  simp [joinWith, meetWith_eq_undefined_iff]

theorem joinWith_eq_true_iff : joinWith D a b = .true ↔ D ∧ (a = .true ∨ b = .true) := by
  simp [joinWith, meetWith_eq_false_iff]

theorem joinWith_eq_false_iff : joinWith D a b = .false ↔ D ∧ a ≠ .true ∧ b ≠ .true := by
  simp [joinWith, meetWith_eq_true_iff]

theorem inf_eq_meetWith (a b : Trivalent) :
    a ⊓ b = meetWith ((a = .false ∨ b = .false) ∨ (a = .true ∧ b = .true)) a b := by
  cases a <;> cases b <;> decide

theorem sup_eq_joinWith (a b : Trivalent) :
    a ⊔ b = joinWith ((a = .true ∨ b = .true) ∨ (a = .false ∧ b = .false)) a b := by
  cases a <;> cases b <;> decide

end DefinednessConditions

/-! ### Weak Kleene

In the Weak Kleene connectives `undefined` is absorbing, so a compound is undefined as soon as an
operand is. This is [bochvar-1938]'s internal logic, which reads the third value as nonsense, and
[kleene-1952]'s weak tables. -/

/-- In Weak Kleene disjunction `undefined` is absorbing, so both operands must be defined. -/
def joinWeak : Trivalent → Trivalent → Trivalent
  | .true, .true | .true, .false | .false, .true => .true
  | .false, .false => .false
  | _, _ => .undefined

/-- In Weak Kleene conjunction `undefined` is absorbing. -/
def meetWeak : Trivalent → Trivalent → Trivalent
  | .true, .true => .true
  | .true, .false | .false, .true | .false, .false => .false
  | _, _ => .undefined

/-- Weak Kleene conjunction is `meetWith` demanding both operands defined. -/
theorem meetWeak_eq_meetWith (a b : Trivalent) :
    meetWeak a b = meetWith (a ≠ .undefined ∧ b ≠ .undefined) a b := by
  cases a <;> cases b <;> decide

theorem joinWeak_eq_joinWith (a b : Trivalent) :
    joinWeak a b = joinWith (a ≠ .undefined ∧ b ≠ .undefined) a b := by
  cases a <;> cases b <;> decide

theorem meetWeak_comm (a b : Trivalent) : meetWeak a b = meetWeak b a := by
  cases a <;> cases b <;> rfl

theorem joinWeak_comm (a b : Trivalent) : joinWeak a b = joinWeak b a := by
  cases a <;> cases b <;> rfl

theorem meetWeak_assoc (a b c : Trivalent) :
    meetWeak (meetWeak a b) c = meetWeak a (meetWeak b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem meetWeak_true_left (a : Trivalent) : meetWeak .true a = a := by cases a <;> rfl

@[simp] theorem meetWeak_undefined_left (a : Trivalent) : meetWeak .undefined a = .undefined :=
  rfl

@[simp] theorem meetWeak_undefined_right (a : Trivalent) : meetWeak a .undefined = .undefined := by
  cases a <;> rfl

@[simp] theorem meetWeak_eq_undefined_iff (a b : Trivalent) :
    meetWeak a b = .undefined ↔ a = .undefined ∨ b = .undefined := by
  cases a <;> cases b <;> decide

@[simp] theorem meetWeak_eq_true_iff (a b : Trivalent) :
    meetWeak a b = .true ↔ a = .true ∧ b = .true := by
  cases a <;> cases b <;> decide

@[simp] theorem meetWeak_eq_false_iff (a b : Trivalent) :
    meetWeak a b = .false ↔ (a = .false ∧ b ≠ .undefined) ∨ (a ≠ .undefined ∧ b = .false) := by
  cases a <;> cases b <;> decide

theorem joinWeak_eq_undefined_iff (a b : Trivalent) :
    joinWeak a b = .undefined ↔ a = .undefined ∨ b = .undefined := by
  cases a <;> cases b <;> decide

theorem joinWeak_eq_false_iff (a b : Trivalent) :
    joinWeak a b = .false ↔ a = .false ∧ b = .false := by
  cases a <;> cases b <;> decide

theorem joinWeak_eq_true_iff (a b : Trivalent) :
    joinWeak a b = .true ↔ a ≠ .undefined ∧ b ≠ .undefined ∧ (a = .true ∨ b = .true) := by
  cases a <;> cases b <;> decide

theorem compl_meetWeak_of_ne_false {a : Trivalent} (h : a ≠ .false) (b : Trivalent) :
    (meetWeak a b)ᶜ = meetWeak a bᶜ := by
  revert h; cases a <;> cases b <;> decide

/-! ### Assertion and presupposition

The assertion operator 𝒜 of [bochvar-1938] sends `undefined` to `false`, closing a value to a
bivalent one, and is `ofProp (a = .true)`. The presupposition operator ∂ of [beaver-1992] sends
`false` to `undefined`, keeping only truth, and is `a ⊔ .undefined`. The binary presupposition
operator is the transplication `π / φ` of [blamey-1986] ([beaver-krahmer-2001] Definition 3), the
value of `φ` where `π` is true and `undefined` elsewhere. [beaver-krahmer-2001] build
presupposition projection from these. -/

theorem sup_undefined_eq_true_iff {a : Trivalent} : a ⊔ .undefined = .true ↔ a = .true := by
  cases a <;> decide

theorem sup_undefined_eq_undefined_iff {a : Trivalent} :
    a ⊔ .undefined = .undefined ↔ a ≠ .true := by
  cases a <;> decide

theorem sup_undefined_ne_false (a : Trivalent) : a ⊔ .undefined ≠ .false := by cases a <;> decide

/-- The transplication `π / φ` of [blamey-1986], `φ` presupposing `π`: the value of `φ` if `π` is
true, `undefined` otherwise ([beaver-krahmer-2001] Definition 3). -/
def transplication : Trivalent → Trivalent → Trivalent
  | .true, b => b
  | _, _ => .undefined

theorem transplication_eq_ite (a b : Trivalent) :
    transplication a b = if a = .true then b else .undefined := by
  cases a <;> rfl

@[simp] theorem transplication_true_left (b : Trivalent) : transplication .true b = b := rfl

@[simp] theorem transplication_false_left (b : Trivalent) :
    transplication .false b = .undefined := rfl

@[simp] theorem transplication_undefined_left (b : Trivalent) :
    transplication .undefined b = .undefined := rfl

@[simp] theorem transplication_eq_true_iff {a b : Trivalent} :
    transplication a b = .true ↔ a = .true ∧ b = .true := by
  cases a <;> cases b <;> decide

@[simp] theorem transplication_eq_false_iff {a b : Trivalent} :
    transplication a b = .false ↔ a = .true ∧ b = .false := by
  cases a <;> cases b <;> decide

@[simp] theorem transplication_eq_undefined_iff {a b : Trivalent} :
    transplication a b = .undefined ↔ a ≠ .true ∨ b = .undefined := by
  cases a <;> cases b <;> decide

/-- Beaver's presupposition operator is the diagonal of transplication. -/
theorem transplication_self (a : Trivalent) : transplication a a = a ⊔ .undefined := by
  cases a <;> rfl

/-- Transplication is definable from Beaver's presupposition operator and the Strong Kleene
connectives, `π / φ = (∂π ∧ φ) ∨ ¬∂π` ([beaver-krahmer-2001] p. 151). -/
theorem transplication_eq (a b : Trivalent) :
    transplication a b = (a ⊔ .undefined) ⊓ b ⊔ (a ⊔ .undefined)ᶜ := by
  cases a <;> cases b <;> rfl

/-! ### Middle Kleene

The Middle Kleene connectives of [peters-1979] read their operands from left to right. An
undefined first operand absorbs, and a defined one proceeds by Strong Kleene, the three-valued
counterpart of Karttunen's filtering ([beaver-krahmer-2001]). Peters stipulates the tables, and
[george-2014] derives them as the Peters-Kleene deployments of the classical connectives
(`Trivalent.deploy₂_and`, `Trivalent.deploy₂_or`, `Trivalent.deploy₂_imp` in
`Linglib.Logic.Trivalent.Deployment`). -/

/-- In Middle Kleene conjunction a left undefined operand absorbs and a defined one proceeds by
Strong Kleene, so `meetMiddle .false .undefined = .false` but
`meetMiddle .undefined .false = .undefined`. -/
def meetMiddle : Trivalent → Trivalent → Trivalent
  | .undefined, _ => .undefined
  | a, b => a ⊓ b

/-- In Middle Kleene disjunction a left undefined operand absorbs and a defined one proceeds by
Strong Kleene, so a defined first disjunct can settle the result when the second is undefined. -/
def joinMiddle : Trivalent → Trivalent → Trivalent
  | .undefined, _ => .undefined
  | a, b => a ⊔ b

theorem meetMiddle_eq_meetWith (a b : Trivalent) :
    meetMiddle a b = meetWith (a ≠ .undefined ∧ (a = .false ∨ b ≠ .undefined)) a b := by
  cases a <;> cases b <;> decide

theorem joinMiddle_eq_joinWith (a b : Trivalent) :
    joinMiddle a b = joinWith (a ≠ .undefined ∧ (a = .true ∨ b ≠ .undefined)) a b := by
  cases a <;> cases b <;> decide

theorem meetMiddle_not_comm : ¬ ∀ a b : Trivalent, meetMiddle a b = meetMiddle b a :=
  fun h ↦ absurd (h .false .undefined) (by decide)

theorem joinMiddle_not_comm : ¬ ∀ a b : Trivalent, joinMiddle a b = joinMiddle b a :=
  fun h ↦ absurd (h .true .undefined) (by decide)

theorem meetMiddle_eq_inf_of_left_ne_undefined (a b : Trivalent) (h : a ≠ .undefined) :
    meetMiddle a b = a ⊓ b := by
  cases a with | undefined => exact absurd rfl h | false => rfl | true => rfl

theorem joinMiddle_eq_sup_of_left_ne_undefined (a b : Trivalent) (h : a ≠ .undefined) :
    joinMiddle a b = a ⊔ b := by
  cases a with | undefined => exact absurd rfl h | false => rfl | true => rfl

@[simp] theorem meetMiddle_undefined_left (a : Trivalent) :
    meetMiddle .undefined a = .undefined := rfl

@[simp] theorem joinMiddle_undefined_left (a : Trivalent) :
    joinMiddle .undefined a = .undefined := rfl

@[simp] theorem meetMiddle_true_left (a : Trivalent) : meetMiddle .true a = a := by
  cases a <;> rfl

@[simp] theorem meetMiddle_false_left (a : Trivalent) : meetMiddle .false a = .false := by
  cases a <;> rfl

@[simp] theorem joinMiddle_false_left (a : Trivalent) : joinMiddle .false a = a := by
  cases a <;> rfl

@[simp] theorem joinMiddle_true_left (a : Trivalent) : joinMiddle .true a = .true := by
  cases a <;> rfl

@[simp] theorem meetMiddle_true_right (a : Trivalent) : meetMiddle a .true = a := by
  cases a <;> rfl

theorem meetMiddle_congr_right {a b b' : Trivalent} (h : a = .true → b = b') :
    meetMiddle a b = meetMiddle a b' := by
  cases a with
  | undefined => rfl
  | false => simp only [meetMiddle_false_left]
  | true => rw [h rfl]

theorem joinMiddle_congr_right {a b b' : Trivalent} (h : a = .false → b = b') :
    joinMiddle a b = joinMiddle a b' := by
  cases a with
  | undefined => rfl
  | false => rw [h rfl]
  | true => simp only [joinMiddle_true_left]

@[simp] theorem meetMiddle_eq_true_iff {a b : Trivalent} :
    meetMiddle a b = .true ↔ a = .true ∧ b = .true := by
  cases a <;> cases b <;> decide

@[simp] theorem meetMiddle_eq_undefined_iff {a b : Trivalent} :
    meetMiddle a b = .undefined ↔ a = .undefined ∨ a = .true ∧ b = .undefined := by
  cases a <;> cases b <;> decide

@[simp] theorem meetMiddle_eq_false_iff {a b : Trivalent} :
    meetMiddle a b = .false ↔ a = .false ∨ a = .true ∧ b = .false := by
  cases a <;> cases b <;> decide

@[simp] theorem joinMiddle_eq_true_iff {a b : Trivalent} :
    joinMiddle a b = .true ↔ a = .true ∨ a = .false ∧ b = .true := by
  cases a <;> cases b <;> decide

@[simp] theorem joinMiddle_eq_undefined_iff {a b : Trivalent} :
    joinMiddle a b = .undefined ↔ a = .undefined ∨ a = .false ∧ b = .undefined := by
  cases a <;> cases b <;> decide

@[simp] theorem joinMiddle_eq_false_iff {a b : Trivalent} :
    joinMiddle a b = .false ↔ a = .false ∧ b = .false := by
  cases a <;> cases b <;> decide

/-! ### Belnap's connectives

The connectives of [belnap-1970]'s conditional assertion skip undefined operands: a compound is
assertive iff at least one operand is, and asserts the combination of the assertive operands only,
so `undefined` is the identity. Strong Kleene's let `undefined` through unless an operand settles
the value, and Weak Kleene's always do. -/

/-- Belnap conjunction skips undefined operands, with `undefined` as identity ([belnap-1970], (8)).
-/
def meetBelnap : Trivalent → Trivalent → Trivalent
  | .undefined, b => b
  | a, .undefined => a
  | a, b => a ⊓ b

/-- Belnap disjunction skips undefined operands, with `undefined` as identity ([belnap-1970], (9)).
-/
def joinBelnap : Trivalent → Trivalent → Trivalent
  | .undefined, b => b
  | a, .undefined => a
  | a, b => a ⊔ b

theorem meetBelnap_eq_meetWith (a b : Trivalent) :
    meetBelnap a b = meetWith (a ≠ .undefined ∨ b ≠ .undefined) a b := by
  cases a <;> cases b <;> decide

theorem joinBelnap_eq_joinWith (a b : Trivalent) :
    joinBelnap a b = joinWith (a ≠ .undefined ∨ b ≠ .undefined) a b := by
  cases a <;> cases b <;> decide

@[simp] theorem meetBelnap_undefined_left (a : Trivalent) : meetBelnap .undefined a = a := rfl

@[simp] theorem meetBelnap_undefined_right (a : Trivalent) : meetBelnap a .undefined = a := by
  cases a <;> rfl

theorem meetBelnap_comm (a b : Trivalent) : meetBelnap a b = meetBelnap b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem joinBelnap_undefined_left (a : Trivalent) : joinBelnap .undefined a = a := rfl

@[simp] theorem joinBelnap_undefined_right (a : Trivalent) : joinBelnap a .undefined = a := by
  cases a <;> rfl

theorem joinBelnap_comm (a b : Trivalent) : joinBelnap a b = joinBelnap b a := by
  cases a <;> cases b <;> rfl

theorem meetBelnap_eq_inf_of_ne_undefined {a b : Trivalent} (ha : a ≠ .undefined)
    (hb : b ≠ .undefined) : meetBelnap a b = a ⊓ b := by
  revert ha hb; cases a <;> cases b <;> decide

@[simp] theorem meetBelnap_eq_undefined_iff {a b : Trivalent} :
    meetBelnap a b = .undefined ↔ a = .undefined ∧ b = .undefined := by
  cases a <;> cases b <;> decide

@[simp] theorem meetBelnap_eq_true_iff {a b : Trivalent} :
    meetBelnap a b = .true ↔ a ≠ .false ∧ b ≠ .false ∧ (a = .true ∨ b = .true) := by
  cases a <;> cases b <;> decide

@[simp] theorem meetBelnap_eq_false_iff {a b : Trivalent} :
    meetBelnap a b = .false ↔ a = .false ∨ b = .false := by
  cases a <;> cases b <;> decide

@[simp] theorem joinBelnap_eq_undefined_iff {a b : Trivalent} :
    joinBelnap a b = .undefined ↔ a = .undefined ∧ b = .undefined := by
  cases a <;> cases b <;> decide

@[simp] theorem joinBelnap_eq_true_iff {a b : Trivalent} :
    joinBelnap a b = .true ↔ a = .true ∨ b = .true := by
  cases a <;> cases b <;> decide

@[simp] theorem joinBelnap_eq_false_iff {a b : Trivalent} :
    joinBelnap a b = .false ↔ a ≠ .true ∧ b ≠ .true ∧ (a = .false ∨ b = .false) := by
  cases a <;> cases b <;> decide

theorem joinBelnap_eq_sup_of_ne_undefined {a b : Trivalent} (ha : a ≠ .undefined)
    (hb : b ≠ .undefined) : joinBelnap a b = a ⊔ b := by
  revert ha hb; cases a <;> cases b <;> decide

theorem undefined_le_meetBelnap_iff {a b : Trivalent} :
    .undefined ≤ meetBelnap a b ↔ .undefined ≤ a ∧ .undefined ≤ b := by
  cases a <;> cases b <;> decide

/-! ### Conditional assertion

A conditional assertion asserts its consequent where its antecedent holds and is void elsewhere
([belnap-1970]). Over a trivalent antecedent a designation standard decides what a void antecedent
does: at K3 only a true antecedent passes the consequent on, the conditional of [de-finetti-1936],
and at LP a void antecedent does too, the conditional of [cooper-1968]. At either standard the
conditional commutes with negation and imports and exports a conjunction. -/

/-- The conditional assertion of `b` on `a` at the standard `d` is `b` where `a` is designated and
`undefined` elsewhere. -/
def condAssert (d : Designation) (a b : Trivalent) : Trivalent :=
  if d.threshold ≤ a then b else .undefined

/-- At K3 the conditional assertion is transplication: de Finetti's conditional and
[blamey-1986]'s binary presupposition operator are one table. -/
theorem condAssert_k3 (a b : Trivalent) : condAssert .k3 a b = transplication a b := by
  cases a <;> rfl

section CondAssert

variable {d : Designation} {a a' b c : Trivalent}

theorem condAssert_of_le (h : d.threshold ≤ a) (b : Trivalent) : condAssert d a b = b :=
  ite_eq_left h

theorem condAssert_of_not_le (h : ¬ d.threshold ≤ a) (b : Trivalent) :
    condAssert d a b = .undefined :=
  ite_eq_right h

@[simp] theorem condAssert_true_left (d : Designation) (b : Trivalent) :
    condAssert d .true b = b := by
  cases d <;> rfl

@[simp] theorem condAssert_false_left (d : Designation) (b : Trivalent) :
    condAssert d .false b = .undefined := by
  cases d <;> rfl

@[simp] theorem condAssert_k3_undefined_left (b : Trivalent) :
    condAssert .k3 .undefined b = .undefined := rfl

@[simp] theorem condAssert_lp_undefined_left (b : Trivalent) : condAssert .lp .undefined b = b :=
  rfl

theorem condAssert_eq_true_iff : condAssert d a b = .true ↔ d.threshold ≤ a ∧ b = .true := by
  unfold condAssert; split_ifs with h <;> simp [h]

theorem condAssert_eq_false_iff : condAssert d a b = .false ↔ d.threshold ≤ a ∧ b = .false := by
  unfold condAssert; split_ifs with h <;> simp [h]

theorem condAssert_eq_undefined_iff :
    condAssert d a b = .undefined ↔ (d.threshold ≤ a → b = .undefined) := by
  unfold condAssert; split_ifs with h <;> simp [h]

@[simp] theorem condAssert_ofProp (P : Prop) [Decidable P] (b : Trivalent) :
    condAssert d (ofProp P) b = if P then b else .undefined := by
  by_cases h : P <;> simp [ofProp, h]

theorem condAssert_congr_left (h : d.threshold ≤ a ↔ d.threshold ≤ a') (b : Trivalent) :
    condAssert d a b = condAssert d a' b := by
  simp only [condAssert, h]

/-- Negation commutes with the conditional. -/
@[simp] theorem compl_condAssert : (condAssert d a b)ᶜ = condAssert d a bᶜ := by
  unfold condAssert; split_ifs <;> simp

/-- **Import-Export**: a conditional on `a` of a conditional on `b` is the conditional on the
Strong Kleene conjunction `a ⊓ b`, which is designated exactly when both conjuncts are. -/
theorem condAssert_condAssert : condAssert d a (condAssert d b c) = condAssert d (a ⊓ b) c := by
  by_cases ha : d.threshold ≤ a <;> by_cases hb : d.threshold ≤ b <;>
    simp [condAssert, le_inf_iff, ha, hb]

theorem condAssert_meetBelnap :
    condAssert d a (meetBelnap b c) = meetBelnap (condAssert d a b) (condAssert d a c) := by
  by_cases h : d.threshold ≤ a <;> simp [condAssert_of_le, condAssert_of_not_le, h]

theorem condAssert_joinBelnap :
    condAssert d a (joinBelnap b c) = joinBelnap (condAssert d a b) (condAssert d a c) := by
  by_cases h : d.threshold ≤ a <;> simp [condAssert_of_le, condAssert_of_not_le, h]

end CondAssert

/-! ### Supervaluation

The value of a predicate over a finite family of classical valuations ([van-fraassen-1966]). The
empty family is vacuously both all-true and all-false, and `supervaluation` resolves it to
`true`. -/

section Supervaluation

variable {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P]

/-- The supervaluation of `P` over the family `s` is `true` when `P` holds at every member,
`false` when it fails at every member of a nonempty `s`, and `undefined` otherwise. -/
def supervaluation : Trivalent :=
  if ∀ a ∈ s, P a then .true else if ∃ a ∈ s, P a then .undefined else .false

theorem supervaluation_eq_true_iff : supervaluation s P = .true ↔ ∀ a ∈ s, P a := by
  unfold supervaluation
  split_ifs with h
  · exact iff_of_true rfl h
  all_goals exact iff_of_false (by decide) h

theorem supervaluation_eq_false_iff :
    supervaluation s P = .false ↔ s.Nonempty ∧ ∀ a ∈ s, ¬ P a := by
  unfold supervaluation
  split_ifs with h₁ h₂
  · simp only [false_iff, not_and, not_forall, not_not]
    exact fun ⟨a, ha⟩ ↦ ⟨a, ha, h₁ a ha⟩
  · simp only [false_iff, not_and, not_forall, not_not]
    exact fun _ ↦ let ⟨a, ha, hp⟩ := h₂; ⟨a, ha, hp⟩
  · push Not at h₁ h₂
    obtain ⟨a, ha, -⟩ := h₁
    exact iff_of_true rfl ⟨⟨a, ha⟩, h₂⟩

theorem supervaluation_eq_undefined_iff :
    supervaluation s P = .undefined ↔ (∃ a ∈ s, P a) ∧ ∃ a ∈ s, ¬ P a := by
  unfold supervaluation; split_ifs <;> simp_all

@[simp] theorem supervaluation_empty : supervaluation ∅ P = .true := by simp [supervaluation]

@[simp] theorem supervaluation_singleton (a : α) : supervaluation {a} P = ofProp (P a) := by
  by_cases h : P a <;> simp [supervaluation, ofProp, h]

variable {s P} in
theorem supervaluation_congr {Q : α → Prop} [DecidablePred Q] (h : ∀ a ∈ s, P a ↔ Q a) :
    supervaluation s P = supervaluation s Q := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_
  · simp only [supervaluation_eq_undefined_iff]
    exact and_congr (exists_congr fun a ↦ and_congr_right (h a))
      (exists_congr fun a ↦ and_congr_right fun ha ↦ not_congr (h a ha))
  · simp only [supervaluation_eq_true_iff]
    exact forall₂_congr h

theorem supervaluation_image {β : Type*} [DecidableEq β] (f : α → β) (Q : β → Prop)
    [DecidablePred Q] : supervaluation (s.image f) Q = supervaluation s (Q ∘ f) := by
  refine eq_of_eq_undefined_iff_of_eq_true_iff ?_ ?_ <;>
    simp [supervaluation_eq_undefined_iff, supervaluation_eq_true_iff]

variable {s} in
theorem supervaluation_const (hs : s.Nonempty) (q : Prop) [Decidable q] :
    supervaluation s (fun _ ↦ q) = ofProp q := by
  by_cases h : q <;> simp [supervaluation, ofProp, h]
  exact hs

variable {s} in
theorem supervaluation_not (hs : s.Nonempty) :
    supervaluation s (¬ P ·) = (supervaluation s P)ᶜ := by
  cases h : supervaluation s P
  · exact (supervaluation_eq_true_iff ..).2 ((supervaluation_eq_false_iff ..).1 h).2
  · obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (supervaluation_eq_undefined_iff ..).1 h
    exact (supervaluation_eq_undefined_iff ..).2 ⟨⟨b, hb, hn⟩, a, ha, not_not.2 hp⟩
  · exact (supervaluation_eq_false_iff ..).2
      ⟨hs, fun a ha hn ↦ hn ((supervaluation_eq_true_iff ..).1 h a ha)⟩

/-- Every value is the supervaluation of its designation at the two standards, `true` designated
at both, `false` at neither, and `undefined` at LP alone. -/
@[simp] theorem supervaluation_threshold_le (a : Trivalent) :
    supervaluation Finset.univ (fun d : Designation ↦ d.threshold ≤ a) = a := by
  cases a <;> decide

end Supervaluation

/-! ### Truth-table interpretations

The trivalent logics of the literature share Kleene's negation and differ in the truth tables of
their binary connectives, which `Connectives` collects. With a designation standard they make a
logical matrix. -/

/-- An interpretation of the binary connectives by trivalent truth tables; negation is always
Kleene's. -/
structure Connectives where
  /-- The conjunction. -/
  conj : Trivalent → Trivalent → Trivalent
  /-- The disjunction. -/
  disj : Trivalent → Trivalent → Trivalent
  /-- The conditional. -/
  cond : Trivalent → Trivalent → Trivalent

namespace Connectives

/-- The strong tables of [kleene-1952], with the material conditional `¬a ∨ b`. -/
@[simps]
def strongKleene : Connectives := ⟨(· ⊓ ·), (· ⊔ ·), fun a b ↦ aᶜ ⊔ b⟩

/-- The weak tables of [kleene-1952], the internal logic of [bochvar-1938]. -/
@[simps]
def weakKleene : Connectives := ⟨meetWeak, joinWeak, fun a b ↦ joinWeak aᶜ b⟩

/-- The Middle Kleene tables of [peters-1979], which read their operands from left to right. -/
@[simps]
def middleKleene : Connectives := ⟨meetMiddle, joinMiddle, fun a b ↦ joinMiddle aᶜ b⟩

/-- The tables of [cooper-1968] take Belnap's conjunction and disjunction, which skip a void
operand, and the conditional that asserts its consequent on a non-false antecedent. -/
@[simps]
def cooper : Connectives := ⟨meetBelnap, joinBelnap, condAssert .lp⟩

/-- The conditional of [de-finetti-1936], which asserts its consequent on a true antecedent, with
the strong Kleene conjunction and disjunction. -/
@[simps]
def deFinetti : Connectives := ⟨(· ⊓ ·), (· ⊔ ·), condAssert .k3⟩

end Connectives

end Trivalent
