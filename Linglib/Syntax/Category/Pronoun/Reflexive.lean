/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Syntax.Binding.Word

/-!
# Reflexive pronouns

A reflexive pronoun is a pronoun whose kind fixes its binding class: it is an anaphor, bound in
its local domain. Some reflexives, as Japanese *zibun* and Icelandic *sig*, also take an
antecedent outside that domain; what licenses the distant antecedent is a matter of analysis and
is not recorded on the entry.

## Main definitions

* `ReflexivePronoun`: a pronoun of the reflexive kind.
* `ReflexivePronoun.toWord`: its token, marked reflexive.

## Main statements

* `ReflexivePronoun.bindingClassOf_toWord`: the token of a reflexive classifies as a reflexive
  anaphor.

## References

* [chomsky-1981]
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

/-- A reflexive pronoun is a reflexive anaphor. -/
@[simp]
theorem bindingClassOf_toWord (p : ReflexivePronoun) :
    Binding.bindingClassOf p.toWord = some .reflexive :=
  Pronoun.bindingClassOf_toWord_reflex _ _

end ReflexivePronoun
