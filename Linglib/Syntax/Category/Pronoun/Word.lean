/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Word.Basic
public import Linglib.Syntax.Category.Pronoun.Indefinite
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# The token of a pronoun

The token of a pronoun is the word with its form and its person, clusivity, number, gender and
case, of the word class and with the pronoun type and reflexive marking its kind supplies. A
personal pronoun's token bears the labels the pronoun agrees as, which can differ from the labels
of its paradigm cell.

## Main definitions

* `Pronoun.toWord`: the token of a pronoun, the pronoun type, reflexive marking and word class
  given.
* `PersonalPronoun.toWord`, `ReflexivePronoun.toWord`, `ReciprocalPronoun.toWord`,
  `InterrogativePronoun.toWord`, `IndefinitePronoun.toWord`: the token of each kind.

## Main results

* `InterrogativePronoun.isWh_toWord`: the token of an interrogative is wh-marked.

## References

* [de-marneffe-zeman-2021]
-/

@[expose] public section

/-- The token of a pronoun is a word with its agreement features, and with the pronoun type,
reflexive marking and word class its kind supplies: a `PRON` unless the kind says otherwise, as
for a pro-adverb. -/
def Pronoun.toWord (p : Pronoun) (pronType : Option UD.PronType := none)
    (reflex : Option Unit := none) (cat : UD.UPOS := .PRON) : Morphology.Word :=
  { form := p.form, cat := cat,
    features := .of (person := p.person) (clusivity := p.clusivity) (number := p.number)
      (gender := p.gender) (case := p.case) (reflex := reflex) (pronType := pronType) }

/-- A personal pronoun's token bears the labels the pronoun agrees as, with its case, and is of
UD pronoun type `Prs`. -/
def PersonalPronoun.toWord (p : PersonalPronoun) : Morphology.Word :=
  { form := p.form, cat := .PRON,
    features := .of (person := p.agreement.person) (clusivity := p.agreement.clusivity)
      (number := p.agreement .number) (gender := p.agreement .gender) (case := p.case)
      (pronType := some .Prs) }

/-- A reflexive's token is of UD pronoun type `Prs` and marked reflexive. -/
def ReflexivePronoun.toWord (p : ReflexivePronoun) : Morphology.Word :=
  p.toPronoun.toWord (some .Prs) (some ())

/-- A reciprocal's token is of UD pronoun type `Rcp`. -/
def ReciprocalPronoun.toWord (p : ReciprocalPronoun) : Morphology.Word :=
  p.toPronoun.toWord (some .Rcp)

/-- The token of a proform has its word class and the pronoun type `t` of its function. -/
def ProForm.toWord (p : ProForm) (t : UD.PronType) : Morphology.Word :=
  p.toPronoun.toWord (some t) (cat := p.cat)

/-- An interrogative's token is of UD pronoun type `Int`. -/
def InterrogativePronoun.toWord (p : InterrogativePronoun) : Morphology.Word :=
  p.toProForm.toWord .Int

/-- The token of an interrogative is wh-marked. -/
theorem InterrogativePronoun.isWh_toWord (p : InterrogativePronoun) : p.toWord.features.IsWh :=
  .inl rfl

/-- An indefinite's token is of UD pronoun type `Ind`. -/
def IndefinitePronoun.toWord (p : IndefinitePronoun) : Morphology.Word :=
  p.toProForm.toWord .Ind
