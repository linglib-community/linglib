module

public import Mathlib.Tactic.DeriveFintype

/-!
# Illocutionary force

The *illocutionary force* of an utterance is the act it performs, the `F` in `F(p)`: an assertion,
a question, a directive, a promise or an exclamation.

## Main definitions

* `SpeechAct.Force`: the illocutionary forces.

## References

* [searle-1969]
-/

@[expose] public section

namespace SpeechAct

/-- The **illocutionary force** of an utterance is the act it performs. -/
inductive Force where
  /-- Putting the content forward as true. -/
  | assertion
  /-- Asking the addressee for information. -/
  | question
  /-- Trying to get the addressee to act, as a command or a request does. -/
  | directive
  /-- Committing the speaker to act. -/
  | promise
  /-- Expressing the speaker's attitude to the content. -/
  | exclamation
  deriving DecidableEq, Repr, Inhabited, Fintype

end SpeechAct
