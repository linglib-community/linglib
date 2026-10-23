module

public import Linglib.Fragments.Turkish.Case
public import Linglib.Syntax.Category.Pronoun.Reciprocal

/-!
# Turkish reciprocal pronouns

The Turkish reciprocal pronoun is the stem *birbir-* 'each other', which is obligatorily
inflected for person with the plural possessive suffixes: *birbirimiz* in the first person,
*birbiriniz* in the second, and *birbiri* or *birbirleri* in the third, where *birbirleri* is
the neutral form for interacting groups and *birbiri* is colloquial. The forms take case
suffixes, with *n* before the suffix in the third person, as in the accusative *birbirlerini*
([goksel-kerslake-2005]). Every form is plural, so a singular noun phrase is no antecedent of a
reciprocal.

As a direct object *birbirleri* stands before the verb and must be bound by a c-commanding
antecedent in its own clause, which is what [bakay-etal-2026] exploit: looks to a candidate at
the reciprocal reflect retrieval and not integration at the verb. The inflected forms of
*kendi-* 'self' have emphatic, reflexive, simple pronominal and resumptive uses
([goksel-kerslake-2005]) and are not entered here.

## Main definitions

* `Turkish.Anaphors.reciprocals` — the person forms of *birbir-*, with the accusative
  *birbirlerini*

## Main results

* `Turkish.Anaphors.number_reciprocals` — every form is plural
* `Turkish.Anaphors.not_candidateAntecedent_of_singular` — a singular nominal is no candidate
  antecedent of a reciprocal

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [Ö. Bakay, F. Akkuş and B. Dillon, *Hierarchical relations guide memory retrieval in sentence
  comprehension: Evidence from a local anaphor in Turkish* (2026)][bakay-etal-2026]
-/

@[expose] public section

namespace Turkish.Anaphors

/-- The first person reciprocal *birbirimiz*. -/
def birbirimiz : ReciprocalPronoun :=
  { form := "birbirimiz", person := some .first, number := some .plural }

/-- The second person reciprocal *birbiriniz*. -/
def birbiriniz : ReciprocalPronoun :=
  { form := "birbiriniz", person := some .second, number := some .plural }

/-- The third person reciprocal *birbirleri*, the neutral form for interacting groups. -/
def birbirleri : ReciprocalPronoun :=
  { form := "birbirleri", person := some .third, number := some .plural }

/-- The third person reciprocal *birbiri*, interchangeable with *birbirleri* of two persons and
colloquial of groups. -/
def birbiri : ReciprocalPronoun :=
  { form := "birbiri", person := some .third, number := some .plural }

/-- The accusative of *birbirleri*, the direct object form of the [bakay-etal-2026] stimuli. -/
def birbirlerini : ReciprocalPronoun :=
  { birbirleri with form := "birbirlerini", cases := {.acc} }

/-- The entered forms of the reciprocal are the four person forms and the accusative of
*birbirleri*. -/
def reciprocals : Finset ReciprocalPronoun :=
  {birbirimiz, birbiriniz, birbirleri, birbiri, birbirlerini}

theorem number_reciprocals : ∀ r ∈ reciprocals, r.number = some .plural := by decide

theorem not_candidateAntecedent_of_singular {r : ReciprocalPronoun} (hr : r ∈ reciprocals)
    {w : Morphology.Word} (hw : w.features .number = some .singular) :
    ¬ r.toPronoun.CandidateAntecedent w :=
  fun h ↦ nomatch h.number_eq (number_reciprocals r hr) hw

end Turkish.Anaphors
