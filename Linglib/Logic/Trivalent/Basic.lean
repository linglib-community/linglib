/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Order.MinMax
public import Linglib.Core.Order.DeMorganAlgebra.Basic

/-!
# Three-valued truth

Three-valued truth adds a value between falsity and truth. Mathlib's `SignType` represents it, with
`-1`, `0` and `1` for false, undefined and true: the order's meet and join are Kleene's strong
conjunction and disjunction, negation is his negation, and multiplication is the biconditional, so
`SignType` is a Kleene algebra that is not Boolean. The other three-valued conjunctions and
disjunctions differ from Kleene's only in when a compound is undefined.

## Main definitions

* `Trivalent.Designation`: the K3 and LP standards, each named by its least designated value.
* `SignType.ofProp`: the two-valued fragment.
* `SignType.meetWith`, `SignType.joinWith`: the conjunction and disjunction undefined exactly
  where a given condition fails.
* `SignType.meetWeak`, `SignType.meetMiddle`, `SignType.meetBelnap` and their joins: the Weak
  Kleene, Middle Kleene and Belnap connectives.
* `SignType.condAssert`: conditional assertion at a designation standard, de Finetti's conditional
  at K3 and Cooper's at LP.
* `SignType.supervaluation`: the value of a predicate over a finite family of valuations.
* `Trivalent.Connectives`: an interpretation of the binary connectives by truth tables, with the
  Strong, Weak and Middle Kleene, Cooper and de Finetti instances.

## Main results

* `SignType.eq_of_eq_zero_iff_of_eq_one_iff`: a value is fixed by whether it is `0` and whether
  it is `1`.
* `Trivalent.Designation.dual_threshold_le_neg_iff`: negation exchanges the K3 and LP standards.
* `SignType.meetWeak_eq_meetWith` and companions: each connective is `meetWith` or `joinWith` at
  its definedness condition.
* `SignType.neg_condAssert`, `SignType.condAssert_condAssert`: conditional assertion commutes with
  negation and satisfies Import-Export.

## Implementation notes

Operations that are expressions in the order and arithmetic get no definition: Strong Kleene
conjunction, disjunction and negation are `⊓`, `⊔` and `-`, exclusive disjunction is `-(a * b)`,
Bochvar's assertion operator is `ofProp (a = 1)`, Beaver's presupposition operator is `a ⊔ 0`,
designation at a standard `d` is `d.threshold ≤ a`, and a Boolean `b` has value `ofProp b`. The
complement of the Kleene algebra is `-`. Every other connective keeps a
pattern-matched definition, so that `rfl` and `decide` evaluate it.

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
* [van-fraassen-1966]
-/

@[expose] public section

namespace SignType

/-! ### Kleene's negation -/

theorem eq_of_eq_zero_iff_of_eq_one_iff {a b : SignType} (h₀ : a = 0 ↔ b = 0)
    (h₁ : a = 1 ↔ b = 1) : a = b := by
  revert h₀ h₁; cases a <;> cases b <;> decide

@[simp] protected theorem neg_zero : -(0 : SignType) = 0 := rfl

attribute [simp] SignType.neg_eq_zero_iff SignType.nonpos_iff_ne_one SignType.nonneg_iff_ne_neg_one

@[simp] protected theorem neg_eq_one_iff {a : SignType} : -a = 1 ↔ a = -1 := by
  cases a <;> decide

@[simp] protected theorem neg_eq_neg_one_iff {a : SignType} : -a = -1 ↔ a = 1 := by
  cases a <;> decide

@[simp] protected theorem sup_one (a : SignType) : a ⊔ 1 = 1 := by cases a <;> rfl
@[simp] protected theorem one_sup (a : SignType) : 1 ⊔ a = 1 := by cases a <;> rfl
@[simp] protected theorem inf_neg_one (a : SignType) : a ⊓ -1 = -1 := by cases a <;> rfl
@[simp] protected theorem neg_one_inf (a : SignType) : -1 ⊓ a = -1 := by cases a <;> rfl

@[simp] protected theorem neg_one_ne_one : (-1 : SignType) ≠ 1 := by decide
@[simp] protected theorem one_ne_neg_one : (1 : SignType) ≠ -1 := by decide
@[simp] protected theorem neg_one_ne_zero : (-1 : SignType) ≠ 0 := by decide
@[simp] protected theorem zero_ne_neg_one : (0 : SignType) ≠ -1 := by decide

@[simp] protected theorem inf_one (a : SignType) : a ⊓ 1 = a := by cases a <;> rfl
@[simp] protected theorem one_inf (a : SignType) : 1 ⊓ a = a := by cases a <;> rfl
@[simp] protected theorem sup_neg_one (a : SignType) : a ⊔ -1 = a := by cases a <;> rfl
@[simp] protected theorem neg_one_sup (a : SignType) : -1 ⊔ a = a := by cases a <;> rfl

@[simp] theorem inf_eq_one_iff {a b : SignType} : a ⊓ b = 1 ↔ a = 1 ∧ b = 1 := by
  cases a <;> cases b <;> decide

@[simp] theorem sup_eq_neg_one_iff {a b : SignType} : a ⊔ b = -1 ↔ a = -1 ∧ b = -1 := by
  cases a <;> cases b <;> decide

@[simp] theorem sup_eq_one_iff {a b : SignType} : a ⊔ b = 1 ↔ a = 1 ∨ b = 1 := by
  cases a <;> cases b <;> decide

@[simp] theorem inf_eq_neg_one_iff {a b : SignType} : a ⊓ b = -1 ↔ a = -1 ∨ b = -1 := by
  cases a <;> cases b <;> decide

@[simp] theorem inf_eq_zero_iff {a b : SignType} :
    a ⊓ b = 0 ↔ a = 0 ∧ b ≠ -1 ∨ b = 0 ∧ a ≠ -1 := by
  cases a <;> cases b <;> decide

@[simp] theorem sup_eq_zero_iff {a b : SignType} :
    a ⊔ b = 0 ↔ a = 0 ∧ b ≠ 1 ∨ b = 0 ∧ a ≠ 1 := by
  cases a <;> cases b <;> decide

theorem neg_antitone : Antitone (Neg.neg : SignType → SignType) := fun _ _ ↦
  SignType.neg_le_neg_iff.2

@[simp] protected theorem neg_inf (a b : SignType) : -(a ⊓ b) = -a ⊔ -b :=
  neg_antitone.map_min

@[simp] protected theorem neg_sup (a b : SignType) : -(a ⊔ b) = -a ⊓ -b :=
  neg_antitone.map_max

/-- Negation is the complement of the Kleene algebra. -/
instance : InvolutiveCompl SignType where
  compl := Neg.neg
  compl_compl := neg_neg
  compl_le_compl h := neg_antitone h

@[simp] theorem compl_eq_neg (a : SignType) : aᶜ = -a := rfl

/-- `SignType` is [kalman-1958]'s three-element Kleene algebra. -/
instance : IsKleene SignType := ⟨by decide⟩

theorem inf_compl_zero_ne_bot : (0 : SignType) ⊓ 0ᶜ ≠ ⊥ := by decide

/-! ### The two-valued fragment -/

/-- The value of a decidable proposition is `1` or `-1`. -/
def ofProp (P : Prop) [Decidable P] : SignType := if P then 1 else -1

section OfProp

variable {P Q : Prop} [Decidable P] [Decidable Q]

@[simp] theorem ofProp_eq_one_iff : ofProp P = 1 ↔ P := by
  by_cases h : P <;> simp [ofProp, h]

@[simp] theorem ofProp_eq_neg_one_iff : ofProp P = -1 ↔ ¬ P := by
  by_cases h : P <;> simp [ofProp, h]

@[simp] theorem ofProp_ne_zero : ofProp P ≠ 0 := by
  by_cases h : P <;> simp [ofProp, h]

@[simp] theorem zero_le_ofProp_iff : 0 ≤ ofProp P ↔ P := by
  by_cases h : P <;> simp [ofProp, h]

theorem ofProp_eq_one_of_ne_zero {a : SignType} [Decidable (a = 1)] (h : a ≠ 0) :
    ofProp (a = 1) = a := by
  revert h; cases a <;> simp

@[congr] theorem ofProp_congr (h : P ↔ Q) : ofProp P = ofProp Q :=
  eq_of_eq_zero_iff_of_eq_one_iff (by simp) (by simp [h])

@[simp] theorem ofProp_true : ofProp True = 1 := rfl

@[simp] theorem ofProp_false : ofProp False = -1 := rfl

@[simp] theorem ofProp_and : ofProp (P ∧ Q) = ofProp P ⊓ ofProp Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [ofProp, hP, hQ]

@[simp] theorem ofProp_or : ofProp (P ∨ Q) = ofProp P ⊔ ofProp Q := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [ofProp, hP, hQ]

@[simp] theorem ofProp_not : ofProp (¬ P) = -ofProp P := by
  by_cases h : P <;> simp [ofProp, h]

end OfProp

end SignType

/-! ### Designated values

Matrix semantics fixes an upward-closed set of *designated* values; on a chain every such set is
principal, so a designation standard is just a threshold, and a value `v` is designated at `d`
when `d.threshold ≤ v`. K3, Strong Kleene logic, designates
`{1}` and preserves truth; LP, [priest-1979]'s Logic of Paradox, designates `{0, 1}` and preserves
non-falsity. The two standards give dual logics over one algebra ([cobreros-etal-2012]), and every
law of designation is a law of the order. -/

namespace Trivalent

/-- A designation standard, identified by its least designated value (`threshold`). -/
inductive Designation where
  | k3
  | lp
  deriving Repr, DecidableEq, Inhabited, Fintype

/-- The least designated value of a standard. -/
def Designation.threshold : Designation → SignType
  | .k3 => 1
  | .lp => 0

/-- The K3/LP duality as an involution on standards. -/
def Designation.dual : Designation → Designation
  | .k3 => .lp
  | .lp => .k3

@[simp] theorem Designation.dual_dual (d : Designation) : d.dual.dual = d := by
  cases d <;> rfl

@[simp] theorem Designation.dual_k3 : Designation.k3.dual = .lp := rfl
@[simp] theorem Designation.dual_lp : Designation.lp.dual = .k3 := rfl

@[simp] theorem Designation.threshold_k3 : Designation.k3.threshold = 1 := rfl
@[simp] theorem Designation.threshold_lp : Designation.lp.threshold = 0 := rfl

theorem Designation.dual_threshold_le_neg_iff (d : Designation) (v : SignType) :
    d.dual.threshold ≤ -v ↔ ¬ d.threshold ≤ v := by
  cases d <;> cases v <;> decide

theorem Designation.threshold_le_ofProp_iff (d : Designation) (P : Prop) [Decidable P] :
    d.threshold ≤ SignType.ofProp P ↔ P := by
  cases d <;> by_cases h : P <;> simp [SignType.ofProp, h]

end Trivalent

namespace SignType

/-! ### Definedness conditions

The binary conjunctions share one truth rule, false when either operand is and true otherwise,
and differ only in where they are undefined. Strong Kleene conjunction is defined whenever the
operands settle the value, Weak Kleene's demands both operands defined, Belnap's demands one, and
Middle Kleene's is defined when the left operand is and either settles the value or the right
operand is defined too. `meetWith` makes the conjunction a function of that condition. -/

/-- The conjunction undefined unless `D` holds, and otherwise false exactly when an operand is. -/
def meetWith (D : Prop) [Decidable D] (a b : SignType) : SignType :=
  if D then if a = -1 ∨ b = -1 then -1 else 1 else 0

/-- The disjunction undefined unless `D` holds, the dual of `meetWith`. -/
def joinWith (D : Prop) [Decidable D] (a b : SignType) : SignType :=
  -meetWith D (-a) (-b)

section DefinednessConditions

variable {D : Prop} [Decidable D] {a b : SignType}

theorem meetWith_eq_zero_iff : meetWith D a b = 0 ↔ ¬D := by
  by_cases hD : D <;> by_cases h : a = -1 ∨ b = -1 <;> simp [meetWith, hD, h]

theorem meetWith_eq_neg_one_iff : meetWith D a b = -1 ↔ D ∧ (a = -1 ∨ b = -1) := by
  by_cases hD : D <;> by_cases h : a = -1 ∨ b = -1 <;> simp [meetWith, hD, h]

theorem meetWith_eq_one_iff : meetWith D a b = 1 ↔ D ∧ a ≠ -1 ∧ b ≠ -1 := by
  rw [show (a ≠ -1 ∧ b ≠ -1) ↔ ¬(a = -1 ∨ b = -1) from not_or.symm]
  by_cases hD : D <;> by_cases h : a = -1 ∨ b = -1 <;> simp [meetWith, hD, h]

theorem joinWith_eq_zero_iff : joinWith D a b = 0 ↔ ¬D := by
  simp [joinWith, SignType.neg_eq_zero_iff, meetWith_eq_zero_iff]

theorem joinWith_eq_one_iff : joinWith D a b = 1 ↔ D ∧ (a = 1 ∨ b = 1) := by
  simp [joinWith, neg_eq_iff_eq_neg, meetWith_eq_neg_one_iff]

theorem joinWith_eq_neg_one_iff : joinWith D a b = -1 ↔ D ∧ a ≠ 1 ∧ b ≠ 1 := by
  simp [joinWith, neg_eq_iff_eq_neg, meetWith_eq_one_iff]

theorem inf_eq_meetWith (a b : SignType) :
    a ⊓ b = meetWith ((a = -1 ∨ b = -1) ∨ (a = 1 ∧ b = 1)) a b := by
  cases a <;> cases b <;> decide

theorem sup_eq_joinWith (a b : SignType) :
    a ⊔ b = joinWith ((a = 1 ∨ b = 1) ∨ (a = -1 ∧ b = -1)) a b := by
  cases a <;> cases b <;> decide

end DefinednessConditions

/-! ### Weak Kleene

In the Weak Kleene connectives `0` is absorbing, so a compound is undefined as soon as an operand
is. This is [bochvar-1938]'s internal logic, which reads the third value as nonsense, and
[kleene-1952]'s weak tables. -/

/-- In Weak Kleene disjunction `0` is absorbing, so both operands must be defined. -/
def joinWeak : SignType → SignType → SignType
  | .pos, .pos | .pos, .neg | .neg, .pos => 1
  | .neg, .neg => -1
  | _, _ => 0

/-- In Weak Kleene conjunction `0` is absorbing. -/
def meetWeak : SignType → SignType → SignType
  | .pos, .pos => 1
  | .pos, .neg | .neg, .pos | .neg, .neg => -1
  | _, _ => 0

theorem meetWeak_eq_meetWith (a b : SignType) :
    meetWeak a b = meetWith (a ≠ 0 ∧ b ≠ 0) a b := by
  cases a <;> cases b <;> decide

theorem joinWeak_eq_joinWith (a b : SignType) :
    joinWeak a b = joinWith (a ≠ 0 ∧ b ≠ 0) a b := by
  cases a <;> cases b <;> decide

theorem meetWeak_comm (a b : SignType) : meetWeak a b = meetWeak b a := by
  cases a <;> cases b <;> rfl

theorem joinWeak_comm (a b : SignType) : joinWeak a b = joinWeak b a := by
  cases a <;> cases b <;> rfl

theorem meetWeak_assoc (a b c : SignType) :
    meetWeak (meetWeak a b) c = meetWeak a (meetWeak b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp] theorem meetWeak_one_left (a : SignType) : meetWeak 1 a = a := by cases a <;> rfl

@[simp] theorem meetWeak_zero_left (a : SignType) : meetWeak 0 a = 0 := rfl

@[simp] theorem meetWeak_zero_right (a : SignType) : meetWeak a 0 = 0 := by cases a <;> rfl

@[simp] theorem meetWeak_eq_zero_iff (a b : SignType) :
    meetWeak a b = 0 ↔ a = 0 ∨ b = 0 := by
  cases a <;> cases b <;> decide

@[simp] theorem meetWeak_eq_one_iff (a b : SignType) :
    meetWeak a b = 1 ↔ a = 1 ∧ b = 1 := by
  cases a <;> cases b <;> decide

@[simp] theorem meetWeak_eq_neg_one_iff (a b : SignType) :
    meetWeak a b = -1 ↔ (a = -1 ∧ b ≠ 0) ∨ (a ≠ 0 ∧ b = -1) := by
  cases a <;> cases b <;> decide

theorem joinWeak_eq_zero_iff (a b : SignType) :
    joinWeak a b = 0 ↔ a = 0 ∨ b = 0 := by
  cases a <;> cases b <;> decide

theorem joinWeak_eq_neg_one_iff (a b : SignType) :
    joinWeak a b = -1 ↔ a = -1 ∧ b = -1 := by
  cases a <;> cases b <;> decide

theorem joinWeak_eq_one_iff (a b : SignType) :
    joinWeak a b = 1 ↔ a ≠ 0 ∧ b ≠ 0 ∧ (a = 1 ∨ b = 1) := by
  cases a <;> cases b <;> decide

theorem neg_meetWeak_of_ne_neg_one {a : SignType} (h : a ≠ -1) (b : SignType) :
    -meetWeak a b = meetWeak a (-b) := by
  revert h; cases a <;> cases b <;> decide

/-! ### Assertion and presupposition

The assertion operator 𝒜 of [bochvar-1938] sends `0` to `-1`, closing a value to a bivalent one,
and is `ofProp (a = 1)`. The presupposition operator ∂ of [beaver-1992] sends `-1` to `0`, keeping
only truth, and is `a ⊔ 0`. [beaver-krahmer-2001] build presupposition projection from the two. -/

theorem sup_zero_eq_one_iff {a : SignType} : a ⊔ 0 = 1 ↔ a = 1 := by cases a <;> decide

theorem sup_zero_eq_zero_iff {a : SignType} : a ⊔ 0 = 0 ↔ a ≠ 1 := by cases a <;> decide

theorem sup_zero_ne_neg_one (a : SignType) : a ⊔ 0 ≠ -1 := by cases a <;> decide

/-! ### Middle Kleene

The Middle Kleene connectives of [peters-1979] read their operands from left to right. An
undefined first operand absorbs, and a defined one proceeds by Strong Kleene, the three-valued
counterpart of Karttunen's filtering ([beaver-krahmer-2001]). -/

/-- In Middle Kleene conjunction a left undefined operand absorbs and a defined one proceeds by
Strong Kleene, so `meetMiddle (-1) 0 = -1` but `meetMiddle 0 (-1) = 0`. -/
def meetMiddle : SignType → SignType → SignType
  | .zero, _ => 0
  | a, b => a ⊓ b

/-- In Middle Kleene disjunction a left undefined operand absorbs and a defined one proceeds by
Strong Kleene, so a defined first disjunct can settle the result when the second is undefined. -/
def joinMiddle : SignType → SignType → SignType
  | .zero, _ => 0
  | a, b => a ⊔ b

theorem meetMiddle_eq_meetWith (a b : SignType) :
    meetMiddle a b = meetWith (a ≠ 0 ∧ (a = -1 ∨ b ≠ 0)) a b := by
  cases a <;> cases b <;> decide

theorem joinMiddle_eq_joinWith (a b : SignType) :
    joinMiddle a b = joinWith (a ≠ 0 ∧ (a = 1 ∨ b ≠ 0)) a b := by
  cases a <;> cases b <;> decide

theorem meetMiddle_not_comm : ¬ ∀ a b : SignType, meetMiddle a b = meetMiddle b a :=
  fun h ↦ absurd (h (-1) 0) (by decide)

theorem joinMiddle_not_comm : ¬ ∀ a b : SignType, joinMiddle a b = joinMiddle b a :=
  fun h ↦ absurd (h 1 0) (by decide)

theorem meetMiddle_eq_inf_of_left_ne_zero (a b : SignType) (h : a ≠ 0) :
    meetMiddle a b = a ⊓ b := by
  cases a with | zero => exact absurd rfl h | neg => rfl | pos => rfl

theorem joinMiddle_eq_sup_of_left_ne_zero (a b : SignType) (h : a ≠ 0) :
    joinMiddle a b = a ⊔ b := by
  cases a with | zero => exact absurd rfl h | neg => rfl | pos => rfl

@[simp] theorem meetMiddle_zero_left (a : SignType) : meetMiddle 0 a = 0 := rfl

@[simp] theorem joinMiddle_zero_left (a : SignType) : joinMiddle 0 a = 0 := rfl

@[simp] theorem meetMiddle_one_left (a : SignType) : meetMiddle 1 a = a := by cases a <;> rfl

@[simp] theorem meetMiddle_neg_one_left (a : SignType) : meetMiddle (-1) a = -1 := by
  cases a <;> rfl

@[simp] theorem joinMiddle_neg_one_left (a : SignType) : joinMiddle (-1) a = a := by
  cases a <;> rfl

@[simp] theorem joinMiddle_one_left (a : SignType) : joinMiddle 1 a = 1 := by cases a <;> rfl

@[simp] theorem meetMiddle_one_right (a : SignType) : meetMiddle a 1 = a := by cases a <;> rfl

theorem meetMiddle_congr_right {a b b' : SignType} (h : a = 1 → b = b') :
    meetMiddle a b = meetMiddle a b' := by
  cases a with
  | zero => rfl
  | neg => simp only [neg_eq_neg_one, meetMiddle_neg_one_left]
  | pos => rw [h rfl]

theorem joinMiddle_congr_right {a b b' : SignType} (h : a = -1 → b = b') :
    joinMiddle a b = joinMiddle a b' := by
  cases a with
  | zero => rfl
  | neg => rw [h rfl]
  | pos => simp only [pos_eq_one, joinMiddle_one_left]

@[simp] theorem meetMiddle_eq_one_iff {a b : SignType} : meetMiddle a b = 1 ↔ a = 1 ∧ b = 1 := by
  cases a <;> cases b <;> decide

@[simp] theorem meetMiddle_eq_zero_iff {a b : SignType} :
    meetMiddle a b = 0 ↔ a = 0 ∨ a = 1 ∧ b = 0 := by
  cases a <;> cases b <;> decide

@[simp] theorem meetMiddle_eq_neg_one_iff {a b : SignType} :
    meetMiddle a b = -1 ↔ a = -1 ∨ a = 1 ∧ b = -1 := by
  cases a <;> cases b <;> decide

@[simp] theorem joinMiddle_eq_one_iff {a b : SignType} :
    joinMiddle a b = 1 ↔ a = 1 ∨ a = -1 ∧ b = 1 := by
  cases a <;> cases b <;> decide

@[simp] theorem joinMiddle_eq_zero_iff {a b : SignType} :
    joinMiddle a b = 0 ↔ a = 0 ∨ a = -1 ∧ b = 0 := by
  cases a <;> cases b <;> decide

@[simp] theorem joinMiddle_eq_neg_one_iff {a b : SignType} :
    joinMiddle a b = -1 ↔ a = -1 ∧ b = -1 := by
  cases a <;> cases b <;> decide

/-! ### Belnap's connectives

The connectives of [belnap-1970]'s conditional assertion skip undefined operands: a compound is
assertive iff at least one operand is, and asserts the combination of the assertive operands only,
so `0` is the identity. Strong Kleene's let `0` through unless an operand settles the value, and
Weak Kleene's always do. -/

/-- Belnap conjunction skips undefined operands, with `0` as identity ([belnap-1970], (8)). -/
def meetBelnap : SignType → SignType → SignType
  | .zero, b => b
  | a, .zero => a
  | a, b => a ⊓ b

/-- Belnap disjunction skips undefined operands, with `0` as identity ([belnap-1970], (9)). -/
def joinBelnap : SignType → SignType → SignType
  | .zero, b => b
  | a, .zero => a
  | a, b => a ⊔ b

theorem meetBelnap_eq_meetWith (a b : SignType) :
    meetBelnap a b = meetWith (a ≠ 0 ∨ b ≠ 0) a b := by
  cases a <;> cases b <;> decide

theorem joinBelnap_eq_joinWith (a b : SignType) :
    joinBelnap a b = joinWith (a ≠ 0 ∨ b ≠ 0) a b := by
  cases a <;> cases b <;> decide

@[simp] theorem meetBelnap_zero_left (a : SignType) : meetBelnap 0 a = a := rfl

@[simp] theorem meetBelnap_zero_right (a : SignType) : meetBelnap a 0 = a := by cases a <;> rfl

theorem meetBelnap_comm (a b : SignType) : meetBelnap a b = meetBelnap b a := by
  cases a <;> cases b <;> rfl

@[simp] theorem joinBelnap_zero_left (a : SignType) : joinBelnap 0 a = a := rfl

@[simp] theorem joinBelnap_zero_right (a : SignType) : joinBelnap a 0 = a := by cases a <;> rfl

theorem joinBelnap_comm (a b : SignType) : joinBelnap a b = joinBelnap b a := by
  cases a <;> cases b <;> rfl

theorem meetBelnap_eq_inf_of_ne_zero {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) :
    meetBelnap a b = a ⊓ b := by
  revert ha hb; cases a <;> cases b <;> decide

@[simp] theorem meetBelnap_eq_zero_iff {a b : SignType} : meetBelnap a b = 0 ↔ a = 0 ∧ b = 0 := by
  cases a <;> cases b <;> decide

@[simp] theorem meetBelnap_eq_one_iff {a b : SignType} :
    meetBelnap a b = 1 ↔ a ≠ -1 ∧ b ≠ -1 ∧ (a = 1 ∨ b = 1) := by
  cases a <;> cases b <;> decide

@[simp] theorem meetBelnap_eq_neg_one_iff {a b : SignType} :
    meetBelnap a b = -1 ↔ a = -1 ∨ b = -1 := by
  cases a <;> cases b <;> decide

@[simp] theorem joinBelnap_eq_zero_iff {a b : SignType} : joinBelnap a b = 0 ↔ a = 0 ∧ b = 0 := by
  cases a <;> cases b <;> decide

@[simp] theorem joinBelnap_eq_one_iff {a b : SignType} : joinBelnap a b = 1 ↔ a = 1 ∨ b = 1 := by
  cases a <;> cases b <;> decide

@[simp] theorem joinBelnap_eq_neg_one_iff {a b : SignType} :
    joinBelnap a b = -1 ↔ a ≠ 1 ∧ b ≠ 1 ∧ (a = -1 ∨ b = -1) := by
  cases a <;> cases b <;> decide

theorem joinBelnap_eq_sup_of_ne_zero {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) :
    joinBelnap a b = a ⊔ b := by
  revert ha hb; cases a <;> cases b <;> decide

@[simp] theorem zero_le_meetBelnap_iff {a b : SignType} : 0 ≤ meetBelnap a b ↔ 0 ≤ a ∧ 0 ≤ b := by
  cases a <;> cases b <;> decide

/-! ### Conditional assertion

A conditional assertion asserts its consequent where its antecedent holds and is void elsewhere
([belnap-1970]). Over a trivalent antecedent a designation standard decides what a void antecedent
does: at K3 only a true antecedent passes the consequent on, the conditional of [de-finetti-1936],
and at LP a void antecedent does too, the conditional of [cooper-1968]. At either standard the
conditional commutes with negation and imports and exports a conjunction. -/

/-- The conditional assertion of `b` on `a` at the standard `d` is `b` where `a` is designated and
`0` elsewhere. -/
def condAssert (d : Trivalent.Designation) (a b : SignType) : SignType :=
  if d.threshold ≤ a then b else 0

section CondAssert

variable {d : Trivalent.Designation} {a a' b c : SignType}

theorem condAssert_of_le (h : d.threshold ≤ a) (b : SignType) : condAssert d a b = b :=
  ite_eq_left h

theorem condAssert_of_not_le (h : ¬ d.threshold ≤ a) (b : SignType) : condAssert d a b = 0 :=
  ite_eq_right h

@[simp] theorem condAssert_one_left (d : Trivalent.Designation) (b : SignType) :
    condAssert d 1 b = b := by
  cases d <;> rfl

@[simp] theorem condAssert_neg_one_left (d : Trivalent.Designation) (b : SignType) :
    condAssert d (-1) b = 0 := by
  cases d <;> rfl

@[simp] theorem condAssert_k3_zero_left (b : SignType) : condAssert .k3 0 b = 0 := rfl

@[simp] theorem condAssert_lp_zero_left (b : SignType) : condAssert .lp 0 b = b := rfl

theorem condAssert_eq_one_iff : condAssert d a b = 1 ↔ d.threshold ≤ a ∧ b = 1 := by
  unfold condAssert; split_ifs with h <;> simp [h]

theorem condAssert_eq_neg_one_iff : condAssert d a b = -1 ↔ d.threshold ≤ a ∧ b = -1 := by
  unfold condAssert; split_ifs with h <;> simp [h]

theorem condAssert_eq_zero_iff : condAssert d a b = 0 ↔ (d.threshold ≤ a → b = 0) := by
  unfold condAssert; split_ifs with h <;> simp [h]

@[simp] theorem condAssert_ofProp (P : Prop) [Decidable P] (b : SignType) :
    condAssert d (ofProp P) b = if P then b else 0 := by
  by_cases h : P <;> simp [h]

theorem condAssert_congr_left (h : d.threshold ≤ a ↔ d.threshold ≤ a') (b : SignType) :
    condAssert d a b = condAssert d a' b := by
  simp only [condAssert, h]

@[simp] theorem neg_condAssert : -condAssert d a b = condAssert d a (-b) := by
  unfold condAssert; split_ifs <;> simp

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
empty family is vacuously both all-true and all-false, and `supervaluation` resolves it to `1`. -/

section Supervaluation

variable {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P]

/-- The supervaluation of `P` over the family `s` is `1` when `P` holds at every member, `-1`
when it fails at every member of a nonempty `s`, and `0` otherwise. -/
def supervaluation : SignType :=
  if ∀ a ∈ s, P a then 1 else if ∃ a ∈ s, P a then 0 else -1

theorem supervaluation_eq_one_iff : supervaluation s P = 1 ↔ ∀ a ∈ s, P a := by
  unfold supervaluation
  split_ifs with h
  · exact iff_of_true rfl h
  all_goals exact iff_of_false (by decide) h

theorem supervaluation_eq_neg_one_iff :
    supervaluation s P = -1 ↔ s.Nonempty ∧ ∀ a ∈ s, ¬ P a := by
  unfold supervaluation
  split_ifs with h₁ h₂
  · simp only [false_iff, not_and, not_forall, not_not]
    exact fun ⟨a, ha⟩ ↦ ⟨a, ha, h₁ a ha⟩
  · simp only [false_iff, not_and, not_forall, not_not]
    exact fun _ ↦ let ⟨a, ha, hp⟩ := h₂; ⟨a, ha, hp⟩
  · push Not at h₁ h₂
    obtain ⟨a, ha, -⟩ := h₁
    exact iff_of_true rfl ⟨⟨a, ha⟩, h₂⟩

theorem supervaluation_eq_zero_iff :
    supervaluation s P = 0 ↔ (∃ a ∈ s, P a) ∧ ∃ a ∈ s, ¬ P a := by
  unfold supervaluation; split_ifs <;> simp_all

@[simp] theorem supervaluation_empty : supervaluation ∅ P = 1 := by simp [supervaluation]

@[simp] theorem supervaluation_singleton (a : α) : supervaluation {a} P = ofProp (P a) := by
  by_cases h : P a <;> simp [supervaluation, ofProp, h]

variable {s P} in
theorem supervaluation_congr {Q : α → Prop} [DecidablePred Q] (h : ∀ a ∈ s, P a ↔ Q a) :
    supervaluation s P = supervaluation s Q := by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_
  · simp only [supervaluation_eq_zero_iff]
    exact and_congr (exists_congr fun a ↦ and_congr_right (h a))
      (exists_congr fun a ↦ and_congr_right fun ha ↦ not_congr (h a ha))
  · simp only [supervaluation_eq_one_iff]
    exact forall₂_congr h

theorem supervaluation_image {β : Type*} [DecidableEq β] (f : α → β) (Q : β → Prop)
    [DecidablePred Q] : supervaluation (s.image f) Q = supervaluation s (Q ∘ f) := by
  refine eq_of_eq_zero_iff_of_eq_one_iff ?_ ?_ <;>
    simp [supervaluation_eq_zero_iff, supervaluation_eq_one_iff]

variable {s} in
theorem supervaluation_const (hs : s.Nonempty) (q : Prop) [Decidable q] :
    supervaluation s (fun _ ↦ q) = ofProp q := by
  by_cases h : q <;> simp [supervaluation, ofProp, h]
  exact hs

variable {s} in
theorem supervaluation_not (hs : s.Nonempty) :
    supervaluation s (¬ P ·) = -supervaluation s P := by
  cases h : supervaluation s P
  · obtain ⟨⟨a, ha, hp⟩, b, hb, hn⟩ := (supervaluation_eq_zero_iff ..).1 h
    exact (supervaluation_eq_zero_iff ..).2 ⟨⟨b, hb, hn⟩, a, ha, not_not.2 hp⟩
  · exact (supervaluation_eq_one_iff ..).2 ((supervaluation_eq_neg_one_iff ..).1 h).2
  · exact (supervaluation_eq_neg_one_iff ..).2
      ⟨hs, fun a ha hn ↦ hn ((supervaluation_eq_one_iff ..).1 h a ha)⟩

end Supervaluation

end SignType

namespace Trivalent

open SignType

/-! ### Truth-table interpretations

The trivalent logics of the literature share Kleene's negation and differ in the truth tables of
their binary connectives, which `Connectives` collects. With a designation standard they make a
logical matrix. -/

/-- An interpretation of the binary connectives by trivalent truth tables; negation is always
Kleene's. -/
structure Connectives where
  /-- The conjunction. -/
  conj : SignType → SignType → SignType
  /-- The disjunction. -/
  disj : SignType → SignType → SignType
  /-- The conditional. -/
  cond : SignType → SignType → SignType

namespace Connectives

/-- The strong tables of [kleene-1952], with the material conditional `¬a ∨ b`. -/
@[simps]
def strongKleene : Connectives := ⟨(· ⊓ ·), (· ⊔ ·), fun a b ↦ -a ⊔ b⟩

/-- The weak tables of [kleene-1952], the internal logic of [bochvar-1938]. -/
@[simps]
def weakKleene : Connectives := ⟨meetWeak, joinWeak, fun a b ↦ joinWeak (-a) b⟩

/-- The Middle Kleene tables of [peters-1979], which read their operands from left to right. -/
@[simps]
def middleKleene : Connectives := ⟨meetMiddle, joinMiddle, fun a b ↦ joinMiddle (-a) b⟩

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
