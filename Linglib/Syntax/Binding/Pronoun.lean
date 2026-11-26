/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Binding.Word
public import Linglib.Syntax.Category.Pronoun.Indefinite
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# The binding class of a pronoun

The binding theory sorts nominal tokens into reflexive and reciprocal anaphors, pronominals and
R-expressions, and reads the class off a token's features. This file states the class of the
token of each kind of pronoun: a reflexive is a reflexive anaphor, a reciprocal a reciprocal
anaphor and a personal pronoun a pronominal. Chomsky takes wh-phrases and quantifier expressions
to be R-expressions, so the token of an interrogative or an indefinite is one where its word
class is nominal, as *who* and *someone* are and *where* is not, and is never a pronominal.

A candidate antecedent of a pronoun's token is a nominal token that agrees with it in
φ-features, a pro-form taking its antecedents from a fixed form-class.

## Main definitions

* `Binding.CandidateAntecedent v w`: `w` is a nominal token that agrees with the token `v` in
  φ-features.

## Main results

* `PersonalPronoun.bindingClassOf_toWord`: the token of a personal pronoun is a pronominal.
* `ReflexivePronoun.bindingClassOf_toWord`: the token of a reflexive is a reflexive anaphor.
* `ReciprocalPronoun.bindingClassOf_toWord`: the token of a reciprocal is a reciprocal anaphor.
* `Pronoun.bindingClassOf_toWord_of_isOperator`: the token of a wh-phrase or a quantifier
  expression is an R-expression where its word class is nominal.
* `Binding.CandidateAntecedent.number_eq`: a candidate antecedent has the token's number.

## References

* [L. Bloomfield, *Language* (1933)][bloomfield-1933]
* [N. Chomsky, *Lectures on Government and Binding* (1981)][chomsky-1981]
-/

@[expose] public section

namespace Pronoun

variable (p : Pronoun)

/-- A token marked reflexive classifies as a reflexive anaphor. -/
@[simp]
theorem bindingClassOf_toWord_reflex (t : Option UD.PronType) :
    Binding.bindingClassOf (p.toWord t (some ())) = some .reflexive := by
  simp [Binding.bindingClassOf, toWord, Morphology.Features.of]

/-- A token of reciprocal pronoun type classifies as a reciprocal anaphor. -/
@[simp]
theorem bindingClassOf_toWord_rcp :
    Binding.bindingClassOf (p.toWord (some .Rcp)) = some .reciprocal := by
  simp [Binding.bindingClassOf, toWord, Morphology.Features.of]

/-- Any other pronoun token that is not an operator's classifies as a pronominal. -/
theorem bindingClassOf_toWord {t : Option UD.PronType} (ht : t ≠ some .Rcp)
    (hop : ∀ x, t = some x → ¬ Binding.IsOperator x) :
    Binding.bindingClassOf (p.toWord t) = some .pronoun := by
  rcases t with _ | t <;> (try cases t) <;>
    simp_all +decide [Binding.bindingClassOf, toWord, Morphology.Features.of]

/-- The token of an operator, a wh-phrase or a quantifier expression, classifies as an
R-expression where its word class is nominal, and falls outside the binding theory where it is
not, as a pro-adverb does ([chomsky-1981]). -/
theorem bindingClassOf_toWord_of_isOperator {t : UD.PronType} (ht : Binding.IsOperator t)
    (c : UD.UPOS) :
    Binding.bindingClassOf (p.toWord (some t) none c) =
      if Binding.IsNominal c then some .rExpression else none := by
  rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    simp +decide [Binding.bindingClassOf, toWord, Morphology.Features.of]

end Pronoun

namespace Binding

/-- A candidate antecedent of a token is a nominal token that agrees with it in φ-features: a
pro-form takes its antecedents from a fixed form-class ([bloomfield-1933]). -/
def CandidateAntecedent (v w : Morphology.Word) : Prop :=
  IsNominal w.cat ∧ Compat v.agreement.index w.agreement.index

instance (v w : Morphology.Word) : Decidable (CandidateAntecedent v w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A candidate antecedent has the token's number, where both mark one. -/
theorem CandidateAntecedent.number_eq {v w : Morphology.Word} (h : CandidateAntecedent v w)
    {n m : Number} (hv : v.features .number = some n) (hw : w.features .number = some m) :
    n = m :=
  Flat.compat_iff.mp (h.2.apply ⟨.number, by decide⟩) n hv m hw

end Binding

namespace ProForm

variable (p : ProForm)

/-- The token of an operator, a wh-phrase or a quantifier expression, is an R-expression where
its word class is nominal, as *who* and *someone* are and *where* is not, and is not a
pronominal. -/
theorem bindingClassOf_toWord {t : UD.PronType} (ht : Binding.IsOperator t) :
    Binding.bindingClassOf (p.toWord t) =
      if Binding.IsNominal p.cat then some .rExpression else none :=
  p.toPronoun.bindingClassOf_toWord_of_isOperator ht _

end ProForm

namespace PersonalPronoun

/-- A personal pronoun is a pronominal. -/
@[simp]
theorem bindingClassOf_toWord (p : PersonalPronoun) :
    Binding.bindingClassOf p.toWord = some .pronoun := by
  simp +decide [Binding.bindingClassOf, toWord, Morphology.Features.of]

end PersonalPronoun

namespace ReflexivePronoun

/-- A reflexive pronoun is a reflexive anaphor. -/
@[simp]
theorem bindingClassOf_toWord (p : ReflexivePronoun) :
    Binding.bindingClassOf p.toWord = some .reflexive :=
  Pronoun.bindingClassOf_toWord_reflex _ _

end ReflexivePronoun

/-- A reciprocal pronoun is a reciprocal anaphor. -/
@[simp]
theorem ReciprocalPronoun.bindingClassOf_toWord (p : ReciprocalPronoun) :
    Binding.bindingClassOf p.toWord = some .reciprocal :=
  Pronoun.bindingClassOf_toWord_rcp _

namespace InterrogativePronoun

variable (p : InterrogativePronoun)

/-- An interrogative is an R-expression where its word class is nominal, as *who* is and *where*
is not, and is not a pronominal. -/
@[simp]
theorem bindingClassOf_toWord :
    Binding.bindingClassOf p.toWord =
      if Binding.IsNominal p.cat then some .rExpression else none :=
  p.toProForm.bindingClassOf_toWord (.inl rfl)

end InterrogativePronoun

namespace IndefinitePronoun

/-- An indefinite is a quantifier expression, so an R-expression where its word class is nominal,
as *someone* is and *somewhere* is not, and is not a pronominal ([chomsky-1981]). -/
@[simp]
theorem bindingClassOf_toWord (p : IndefinitePronoun) :
    Binding.bindingClassOf p.toWord =
      if Binding.IsNominal p.cat then some .rExpression else none :=
  p.toProForm.bindingClassOf_toWord (.inr (.inr (.inl rfl)))

end IndefinitePronoun
