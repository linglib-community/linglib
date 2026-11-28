module

public import Linglib.Languages.English.Auxiliaries
public import Linglib.Languages.English.Nouns
public import Linglib.Languages.English.Verbs.Basic
public import Linglib.Morphology.Word.Basic

/-!
# English word tokens

The tokens of English nouns and verbs: a noun in the singular, and a verb in a cell of its
paradigm with the features of the cell. The infinitival marker *to* is entered as a token, a
particle and not a preposition.

## Main definitions

* `English.Nouns.Noun.toWordSg`: the singular token of a noun.
* `English.Verbs.Verb.Cell.features`: the token features of a cell of a verb.
* `English.Verbs.Verb.toWord`: the token of a verb in a cell.
* `English.Auxiliaries.toInf`: the infinitival marker *to*.

## References

* [de-marneffe-zeman-2021]
* [huddleston-pullum-2002]
-/

@[expose] public section

open Morphology

namespace English

/-- The singular token of a noun is a `NOUN`, masculine or feminine by the gender the entry
restricts its referents to, where it does. -/
def Nouns.Noun.toWordSg (n : Nouns.Noun) : Word :=
  { form := n.form, cat := .NOUN
    features := Features.of (number := some .singular)
      (gender := n.referentGender.map ReferentGender.toUD) }

/-- The token features of an inflectional cell of a verb. -/
def Verbs.Verb.Cell.features : Verbs.Verb.Cell → Features
  | .base => Features.of (verbForm := some .Inf)
  | .thirdSg => Features.of (number := some .singular) (person := some .third)
      (voice := some .Act) (verbForm := some .Fin) (tense := some .Pres)
  | .plainPresent => Features.of (voice := some .Act) (verbForm := some .Fin) (tense := some .Pres)
  | .past => Features.of (verbForm := some .Fin) (voice := some .Act) (tense := some .Past)
  | .pastParticiple => Features.of (verbForm := some .Part)
  | .presentParticiple => Features.of (verbForm := some .Part)

/-- The token of a verb in a cell has the entry's form there and the cell's features. -/
def Verbs.Verb.toWord (v : Verbs.Verb) (c : Verbs.Verb.Cell) : Word :=
  { form := v.realize c, cat := .VERB, features := c.features }

/-- The infinitival marker *to*, a particle, distinct from the preposition
`English.Adpositions.to_`: *John managed to sleep*. -/
def Auxiliaries.toInf : Word := { form := "to", cat := .PART }

end English
