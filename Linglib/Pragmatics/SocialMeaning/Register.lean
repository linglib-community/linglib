module

public import Mathlib.Tactic.DeriveFintype

/-!
# Register

This file defines the register of a linguistic form. A register is a recurrent pattern of
variation in linguistic behaviour that a speech community ties to the situation and the purpose
of speech, and speakers move between registers from one situation to the next. Registers differ
along many dimensions. The one recorded here is formality, on the three levels the Cambridge
Grammar calls styles: a form belongs to formal style, to informal style, or is neutral between
them. As a first-person future English *shall* is somewhat more formal than *will*, and the
negative forms *can't* and *won't* are informal and avoided in the most formal styles.

Formality is a property of the situation of use. The deference a form presents toward a person
it refers to or addresses is a separate property, its honorific grade, a coordinate of the
language's own paradigms (`Syntax/Category/Pronoun/Personal.lean`). The Korean speech-style
particles *-supnita* and *-eyo* both present the addressee as above the speaker and differ in
the formality of the discourse.

## Main definitions

* `SocialMeaning.Register`: the informal, neutral and formal styles.

## Implementation notes

The entries that carry a register are neutral unless they say otherwise, so the neutral value
covers a form a grammar calls neutral and a form whose style it does not mention. A form a
grammar confines to writing is entered as formal and one it confines to colloquial speech as
informal, although the medium and the formality of a situation are separate parameters.

## References

* [huddleston-pullum-2002]
* [rotter-liu-2025]
* [alok-bhalla-2026]
-/

@[expose] public section

namespace SocialMeaning

/-- The register of a form is the formality of the situations in which speakers use it. -/
inductive Register where
  /-- Informal style, such as the negative forms *can't* and *won't*. -/
  | informal
  /-- Neutral between formal and informal style. -/
  | neutral
  /-- Formal style, such as *shall* beside *will*. -/
  | formal
  deriving DecidableEq, Fintype, Repr

end SocialMeaning
