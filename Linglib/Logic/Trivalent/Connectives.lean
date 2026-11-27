/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Trivalent.Basic

/-!
# Three-valued connectives

How should *and* treat an operand that has no truth value? The three-valued logics of the literature
answer differently, and the answer decides when a compound sentence inherits the presupposition
failure of a part. The conjunctions agree about truth: a conjunction is false when a conjunct is,
and true otherwise. They differ in when it is undefined. Strong Kleene conjunction is undefined only
when nothing settles its value, and Weak Kleene conjunction whenever a conjunct is undefined. Middle
Kleene conjunction reads from left to right, and Belnap's skips an undefined conjunct. Blamey's
**transplication** is the binary presupposition operator, *φ* presupposing *π*. **Conditional
assertion** asserts its consequent where its antecedent holds, and a **supervaluation** gives the
verdict of a family of classical valuations.

## Implementation notes

Every connective keeps a pattern-matched definition, so that `rfl` and `decide` evaluate it.

`meetWith D` and `joinWith D` are the conjunction and disjunction that are undefined exactly where
the condition `D` fails, and each family is one of them at its definedness condition
(`meetWeak_eq_meetWith` and its companions): the Weak Kleene connectives `meetWeak` and `joinWeak`,
the Middle Kleene connectives `meetMiddle` and `joinMiddle`, and Belnap's `meetBelnap` and
`joinBelnap`. Beaver's presupposition operator is the diagonal of `transplication`
(`transplication_self`), and transplication is definable from it (`transplication_eq`). Conditional
assertion `condAssert d` at a designation standard is de Finetti's conditional at K3, where it is
transplication (`condAssert_k3`), and Cooper's at LP; it commutes with negation (`compl_condAssert`)
and satisfies Import-Export (`condAssert_condAssert`). `supervaluation s P` is the value of a
predicate over a finite family of valuations, and `Connectives` is an interpretation of the binary
connectives by truth tables.

## References

* [kleene-1952]
* [bochvar-1938]
* [peters-1979]
* [belnap-1970]
* [de-finetti-1936]
* [cooper-1968]
* [beaver-1992]
* [beaver-krahmer-2001]
* [blamey-1986]
* [van-fraassen-1966]
* [george-2014]
-/

@[expose] public section

namespace Trivalent

/-!
### Definedness conditions

The conjunctions share one rule for truth: a conjunction is false when a conjunct is, and true
otherwise. They differ only in when it is defined. Strong Kleene's is defined whenever its conjuncts
settle its value, Weak Kleene's when both conjuncts are defined, Belnap's when one is, and Middle
Kleene's when the first conjunct is defined and either settles the value or the second is defined
too.
-/

/-- The **conjunction with definedness condition** *D* is undefined unless *D* holds, and otherwise
false if a conjunct is false and true if neither is. -/
def meetWith (D : Prop) [Decidable D] (a b : Trivalent) : Trivalent :=
  if D then if a = .false ∨ b = .false then .false else .true else .undefined

/-- The **disjunction with definedness condition** *D* is undefined unless *D* holds, and otherwise
true if a disjunct is true and false if neither is. -/
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

/-!
### Weak Kleene

In the Weak Kleene connectives an undefined operand makes the whole undefined. This is Bochvar's
internal logic, which reads the third value as nonsense, and the weak tables of Kleene.
-/

/-- **Weak Kleene disjunction** is undefined when either disjunct is, and classical otherwise. -/
def joinWeak : Trivalent → Trivalent → Trivalent
  | .true, .true | .true, .false | .false, .true => .true
  | .false, .false => .false
  | _, _ => .undefined

/-- **Weak Kleene conjunction** is undefined when either conjunct is, and classical otherwise. -/
def meetWeak : Trivalent → Trivalent → Trivalent
  | .true, .true => .true
  | .true, .false | .false, .true | .false, .false => .false
  | _, _ => .undefined

/-- Weak Kleene conjunction is the conjunction whose definedness condition is that both conjuncts
are defined. -/
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

/-!
### Assertion and presupposition

Bochvar's assertion operator turns undefined into false, so that its result is two-valued. Beaver's
presupposition operator does the reverse and turns false into undefined, keeping only truth.
Blamey's transplication is the binary presupposition operator, with the value of *φ* where *π* is
true and undefined elsewhere ([beaver-krahmer-2001] Definition 3). Beaver and Krahmer build
presupposition projection from these.
-/

theorem sup_undefined_eq_true_iff {a : Trivalent} : a ⊔ .undefined = .true ↔ a = .true := by
  cases a <;> decide

theorem sup_undefined_eq_undefined_iff {a : Trivalent} :
    a ⊔ .undefined = .undefined ↔ a ≠ .true := by
  cases a <;> decide

theorem sup_undefined_ne_false (a : Trivalent) : a ⊔ .undefined ≠ .false := by cases a <;> decide

/-- The **transplication** *π / φ* of [blamey-1986], read as *φ* presupposing *π*, has the value of
*φ* if *π* is true and is undefined otherwise ([beaver-krahmer-2001] Definition 3). -/
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

/-- A value presupposing itself is true if the value is true and undefined otherwise, which is
Beaver's presupposition operator applied to it. -/
theorem transplication_self (a : Trivalent) : transplication a a = a ⊔ .undefined := by
  cases a <;> rfl

/-- Transplication is definable from Beaver's presupposition operator ∂ and the Strong Kleene
connectives, as (∂*π* ∧ *φ*) ∨ ¬∂*π* ([beaver-krahmer-2001] p. 151). -/
theorem transplication_eq (a b : Trivalent) :
    transplication a b = (a ⊔ .undefined) ⊓ b ⊔ (a ⊔ .undefined)ᶜ := by
  cases a <;> cases b <;> rfl

/-!
### Middle Kleene

The Middle Kleene connectives of Peters read their operands from left to right. An undefined first
operand makes the whole undefined, and a defined one lets the Strong Kleene connective decide, the
three-valued counterpart of Karttunen's filtering in Beaver and Krahmer's account. Peters stipulates
the tables, and George derives them from the classical connectives (`Trivalent.deploy₂_and`,
`Trivalent.deploy₂_or`, `Trivalent.deploy₂_imp` in `Linglib.Logic.Trivalent.Deployment`).
-/

/-- **Middle Kleene conjunction** is undefined when its first conjunct is, and is otherwise the
Strong Kleene conjunction. A false first conjunct therefore makes it false even if the second is
undefined, but a false second conjunct does not rescue an undefined first. -/
def meetMiddle : Trivalent → Trivalent → Trivalent
  | .undefined, _ => .undefined
  | a, b => a ⊓ b

/-- **Middle Kleene disjunction** is undefined when its first disjunct is, and is otherwise the
Strong Kleene disjunction. A true first disjunct therefore makes it true even if the second is
undefined. -/
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

/-!
### Belnap's connectives

The connectives of Belnap's conditional assertion skip an undefined operand. A compound asserts
something as soon as one operand does, and what it asserts combines the operands that do. The Strong
Kleene connectives let an undefined operand through unless the other settles the value, and the Weak
Kleene ones always do.
-/

/-- **Belnap conjunction** skips an undefined conjunct and returns the other, and is the Strong
Kleene conjunction when both are defined ([belnap-1970], (8)). -/
def meetBelnap : Trivalent → Trivalent → Trivalent
  | .undefined, b => b
  | a, .undefined => a
  | a, b => a ⊓ b

/-- **Belnap disjunction** skips an undefined disjunct and returns the other, and is the Strong
Kleene disjunction when both are defined ([belnap-1970], (9)). -/
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

/-!
### Conditional assertion

A conditional assertion asserts its consequent where its antecedent holds and asserts nothing
elsewhere, in Belnap's phrase. When the antecedent may itself be undefined, a designation standard
decides whether it holds. At K3 only a true antecedent passes the consequent on, which is de
Finetti's conditional, and at LP an undefined antecedent does too, which is Cooper's. At either
standard the conditional commutes with negation and satisfies Import-Export.
-/

/-- The **conditional assertion** of *b* on *a*, at a designation standard, has the value of *b* if
*a* is designated at that standard and is undefined otherwise. -/
def condAssert (d : Designation) (a b : Trivalent) : Trivalent :=
  if d.threshold ≤ a then b else .undefined

/-- At K3 the conditional assertion of *b* on *a* is the transplication of *b* by *a*, so de
Finetti's conditional and the binary presupposition operator of [blamey-1986] have one truth
table. -/
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

/-- The negation of a conditional assertion is the conditional assertion of the negated consequent
on the same antecedent. -/
@[simp] theorem compl_condAssert : (condAssert d a b)ᶜ = condAssert d a bᶜ := by
  unfold condAssert; split_ifs <;> simp

/-- A conditional assertion on *a* of a conditional assertion on *b* is the conditional assertion on
the Strong Kleene conjunction of *a* and *b*, which is designated exactly when both are. This is
**Import-Export**. -/
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

/-!
### Supervaluation

A supervaluation, van Fraassen's notion, gives the verdict of a family of classical valuations: true
if all make the sentence true, false if all make it false, and undefined if they disagree. An empty
family does both vacuously, and here it counts as true.
-/

section Supervaluation

variable {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P]

/-- The **supervaluation** of a property over a finite family is true if every member has the
property, false if the family is nonempty and no member has it, and undefined otherwise. -/
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

/-- Every truth value is the supervaluation, over the two designation standards, of whether it is
designated. True is designated at both standards, false at neither, and undefined at LP alone. -/
@[simp] theorem supervaluation_threshold_le (a : Trivalent) :
    supervaluation Finset.univ (fun d : Designation ↦ d.threshold ≤ a) = a := by
  cases a <;> decide

end Supervaluation

/-!
### Truth-table interpretations

The three-valued logics of the literature share Kleene's negation and differ in the truth tables of
their binary connectives. An interpretation collects those tables, and with a designation standard
it makes a logical matrix.
-/

/-- An **interpretation** of the binary connectives gives a three-valued truth table for
conjunction, for disjunction and for the conditional. Negation is Kleene's in every
interpretation. -/
structure Connectives where
  /-- The conjunction. -/
  conj : Trivalent → Trivalent → Trivalent
  /-- The disjunction. -/
  disj : Trivalent → Trivalent → Trivalent
  /-- The conditional. -/
  cond : Trivalent → Trivalent → Trivalent

namespace Connectives

/-- The **Strong Kleene interpretation** uses the strong tables of [kleene-1952], with the material
conditional, the disjunction of the negated antecedent with the consequent. -/
@[simps]
def strongKleene : Connectives := ⟨(· ⊓ ·), (· ⊔ ·), fun a b ↦ aᶜ ⊔ b⟩

/-- The **Weak Kleene interpretation** uses the weak tables of [kleene-1952], the internal logic of
[bochvar-1938], with the material conditional built from the weak disjunction. -/
@[simps]
def weakKleene : Connectives := ⟨meetWeak, joinWeak, fun a b ↦ joinWeak aᶜ b⟩

/-- The **Middle Kleene interpretation** uses the tables of [peters-1979], which read their operands
from left to right. -/
@[simps]
def middleKleene : Connectives := ⟨meetMiddle, joinMiddle, fun a b ↦ joinMiddle aᶜ b⟩

/-- The **Cooper interpretation**, after [cooper-1968], uses Belnap's conjunction and disjunction,
which skip an undefined operand, and the conditional that asserts its consequent when its antecedent
is not false. -/
@[simps]
def cooper : Connectives := ⟨meetBelnap, joinBelnap, condAssert .lp⟩

/-- The **de Finetti interpretation** uses the Strong Kleene conjunction and disjunction and the
conditional of [de-finetti-1936], which asserts its consequent when its antecedent is true. -/
@[simps]
def deFinetti : Connectives := ⟨(· ⊓ ·), (· ⊔ ·), condAssert .k3⟩

end Connectives

end Trivalent
