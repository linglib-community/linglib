module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Register

This file defines the register of a linguistic form. A register is a way of speaking that a
speech community ties to a kind of situation, and variation in register is variation within
one speaker across situations rather than between speakers. The formality of the situation is
the dimension recorded here: a form belongs to careful or written language, to casual speech,
or to neither. English *shall* is formal beside *will*, the German simple past is the narrative
tense of writing, and Indonesian *telah* is the written counterpart of *sudah*.

Register is a property of the form and of the situation of use. The deference a form presents
toward a person it refers to or addresses is a separate property, its honorific grade, a
coordinate of the language's own paradigms (`Syntax/Category/Pronoun/Personal.lean`). The Korean
speech-style particles present the same grade to the addressee and differ in the formality of the
discourse.

## Main definitions

* `SocialMeaning.Register`: the informal, neutral and formal registers, linearly ordered by
  formality.

## References

* [huddleston-pullum-2002]
* [rotter-liu-2025]
* [alok-bhalla-2026]
-/

@[expose] public section

namespace SocialMeaning

/-- The register of a form is the formality of the situations in which speakers use it. -/
inductive Register where
  /-- Colloquial, casual speech, such as the negative forms *can't* and *won't*. -/
  | informal
  /-- Unmarked for formality. -/
  | neutral
  /-- Written, literary or careful language, such as *shall*. -/
  | formal
  deriving DecidableEq, Fintype, Repr

namespace Register

/-- Registers are ordered by formality, `informal < neutral < formal`. -/
instance : LinearOrder Register :=
  LinearOrder.lift' Register.ctorIdx fun a b h ↦ by cases a <;> cases b <;> first | rfl | cases h

instance : BoundedOrder Register where
  top := formal
  le_top := by decide
  bot := informal
  bot_le := by decide

end Register

end SocialMeaning
