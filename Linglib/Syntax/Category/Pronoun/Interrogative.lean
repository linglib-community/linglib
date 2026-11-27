/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Pronoun.ProForm

/-!
# Interrogative pronouns

An interrogative pronoun is a proform whose function is to ask: *who* about a person, *what*
about a thing, *where* about a place. Many languages build their indefinite series on their
interrogatives, and in some the same forms serve both functions; a form that is not
interrogative by itself is a plain `ProForm`. The token of an interrogative is
[wh-marked](##InterrogativePronoun.isWh_toWord).

## References

* [haspelmath-1997]
* [bhat-2004]
-/

@[expose] public section

/-- An interrogative pronoun is a `ProForm` of the interrogative kind. -/
@[ext]
structure InterrogativePronoun extends ProForm

instance : DecidableEq InterrogativePronoun :=
  fun _ _ ↦ decidable_of_iff _ InterrogativePronoun.ext_iff.symm

namespace InterrogativePronoun

variable (p : InterrogativePronoun)

/-- An interrogative's word is of UD pronoun type `Int`. -/
def toWord : Morphology.Word := p.toProForm.toWord .Int

/-- An interrogative projects a wh-marked word. -/
theorem isWh_toWord : p.toWord.features.IsWh :=
  .inl rfl


end InterrogativePronoun
