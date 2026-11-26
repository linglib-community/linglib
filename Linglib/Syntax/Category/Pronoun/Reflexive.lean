/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Reflexive pronouns

A reflexive pronoun is a pronoun of the reflexive kind, whose token is marked reflexive. Some
reflexives, as Japanese *zibun* and Icelandic *sig*, also take an
antecedent outside that domain; what licenses the distant antecedent is a matter of analysis and
is not recorded on the entry.

## Main definitions

* `ReflexivePronoun`: a pronoun of the reflexive kind.
* `ReflexivePronoun.toWord`: its token, marked reflexive.

## References

-/

@[expose] public section

/-- A reflexive pronoun is a `Pronoun` of the reflexive kind. -/
@[ext]
structure ReflexivePronoun extends Pronoun

instance : DecidableEq ReflexivePronoun :=
  fun _ _ ↦ decidable_of_iff _ ReflexivePronoun.ext_iff.symm

namespace ReflexivePronoun

/-- A reflexive's token is of UD pronoun type `Prs` and marked reflexive. -/
def toWord (p : ReflexivePronoun) : Morphology.Word := p.toPronoun.toWord (some .Prs) (some ())


end ReflexivePronoun
