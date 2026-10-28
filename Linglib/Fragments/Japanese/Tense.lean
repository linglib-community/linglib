module

public import Linglib.Fragments.Japanese.Morph
public import Linglib.Syntax.Category.Verb.Tense

/-!
# Japanese tense endings

Japanese distinguishes the past from the non-past, and a predicate marks its tense with an ending
of its conjugation. A verb takes the non-past *-(r)u* and the past *-ta*, as in *tabe-ru* 'eats'
and *tabe-ta* 'ate'; an adjective takes *-i* and *-kat-ta*, as in *ooki-i* 'is big' and
*ooki-kat-ta* 'was big'; and a noun or an adjectival noun forms a predicate with the copula,
*-da* and *-dat-ta*, as in *hon-da* 'is a book' and *hon-dat-ta* 'was a book'. The non-past
endings [differ from one conjugation to another](##ending_present_injective), while [every past
ends in the one suffix *-ta*](##getLast?_ending_past), after *-kat-* in an adjective and *-dat-*
in the copula. An ending marks [the past or the non-past](##ending_eq_ending_iff), so the present
and the future share one.

## Main definitions

* `Japanese.Tense.Conjugation`: the verbal, adjectival and nominal conjugations.
* `Japanese.Tense.ending`: the ending by which a conjugation marks a tense.

## Implementation notes

The verbal endings are the inflections `Japanese.Verb.Exponent.u` and
`Japanese.Verb.Exponent.ta` in citation form, so the past *-ta* stands also for its form *-da*
after some stems, as in *yon-da* 'read'. The copula is written as a suffix, as in the paradigm
Tsujimura gives nouns and adjectival nouns together. The adjectival endings the negative takes,
`Japanese.Negation.adjectivalEndings`, leave the past *-katta* unsegmented and [otherwise agree
with these](##negation_adjectivalEndings).

## References

* [tsujimura-2014]
-/

@[expose] public section

namespace Japanese.Tense

open Morphology (Morph)

/-- The conjugations by which Japanese predicates take their tense endings. -/
inductive Conjugation where
  /-- The conjugation of verbs. -/
  | verbal
  /-- The conjugation of adjectives. -/
  | adjectival
  /-- The conjugation of nouns and adjectival nouns, which form predicates with the copula. -/
  | nominal
  deriving DecidableEq, Fintype

/-- The ending by which a conjugation marks a tense after the stem: the verbal non-past *-(r)u*
and past *-ta*, the adjectival *-i* and *-kat-ta*, and the copula *-da* and *-dat-ta*
([tsujimura-2014] (2), (4), (5), (17), (32)). The present and the future share the non-past. -/
def ending : Conjugation → Tense → List Morph
  | .verbal, .past => Verb.Exponent.ta.morphs
  | .verbal, _ => Verb.Exponent.u.morphs
  | .adjectival, .past => [.suff "kat", .suff "ta"]
  | .adjectival, _ => [.suff "i"]
  | .nominal, .past => [.suff "dat", .suff "ta"]
  | .nominal, _ => [.suff "da"]

/-- Every conjugation ends its past in the one suffix *-ta*, the past of the verb, preceded by
*-kat-* in an adjective and by *-dat-* in the copula ([tsujimura-2014] p. 131). -/
theorem getLast?_ending_past (c : Conjugation) :
    (ending c .past).getLast? = some (.suff "ta") := by
  cases c <;> rfl

/-- An ending marks the past or the non-past: two tenses share the ending of a conjugation
exactly when both or neither is the past. -/
theorem ending_eq_ending_iff (c : Conjugation) {t t' : Tense} :
    ending c t = ending c t' ↔ (t = .past ↔ t' = .past) := by
  cases c <;> cases t <;> cases t' <;> decide

/-- The three conjugations have different non-past endings. -/
theorem ending_present_injective : Function.Injective (ending · .present) := by
  decide

/-- The adjectival endings that the negative takes are those of the adjectival conjugation, with
the past *-katta* unsegmented. -/
theorem negation_adjectivalEndings :
    Negation.adjectivalEndings.map Morph.form =
      [Tense.present, .past].map fun t ↦ (ending .adjectival t).foldl (· ++ ·.form) "" := by
  decide

end Japanese.Tense
