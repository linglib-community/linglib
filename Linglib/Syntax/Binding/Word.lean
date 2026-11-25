/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Binding.Basic
public import Linglib.Morphology.Word.Basic

/-!
# The binding class of a word

The binding class of a word is read off its morphology and category: reflexive marking makes a
reflexive, the reciprocal pronoun type a reciprocal, any other pronoun that is not an operator a
pronominal, and an operator or a noun an R-expression.

## Main definitions

* `Binding.IsOperator`: the pronoun types of wh-phrases and quantifier expressions.
* `Binding.bindingClassOf`: the binding class of a word.

## References

* [chomsky-1981]
-/

@[expose] public section

namespace Binding

/-- A pronoun type is an operator's when it is interrogative, relative, indefinite, negative or
total: the types of the wh-phrases and quantifier expressions, which [chomsky-1981] takes to be
R-expressions. -/
def IsOperator (t : UD.PronType) : Prop := t = .Int ∨ t = .Rel ∨ t = .Ind ∨ t = .Neg ∨ t = .Tot

instance : DecidablePred IsOperator :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _))

/-- `bindingClassOf w` reads the binding class of `w` off its morphology and category.
Reflexive marking makes a reflexive, the reciprocal pronoun type a reciprocal, any other pronoun
that is not an operator a pronominal, and an operator or a noun an R-expression. -/
def bindingClassOf (w : Morphology.Word) : Option BindingClass :=
  if (w.features .reflex).isSome then some .reflexive
  else match w.features .pronType with
    | some .Rcp => some .reciprocal
    | t =>
      if w.cat = .PRON ∧ ∀ x, t = some x → ¬ IsOperator x then some .pronoun
      else if IsNominal w.cat then some .rExpression
      else none

end Binding
