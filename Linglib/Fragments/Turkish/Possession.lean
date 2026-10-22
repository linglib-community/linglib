module

public import Linglib.Fragments.Turkish.Morphotactics

/-!
# Turkish possession

Turkish expresses *x has y* by two existential sentences on the predicates *var* 'existent'
and *yok* 'non-existent' (Göksel and Kerslake §12.1.1.2). In the possessive existential
sentence the possessor is genitive and the head of the possessee takes the possessive suffix
of the possessor's person and number, *Murat'ın yatı var* 'Murat has a yacht'; in the
locative existential sentence the possessor is locative and the possessee unmarked, *Bende
bir kitap var* 'I have a book'. Adverbials generally precede the possessee, before or after
the possessor.

## Main definitions

* `Turkish.Possession.var`, `Turkish.Possession.yok`: the existential predicates
* `Turkish.Possession.predicate`: a predicate with its copular marker
* `Turkish.Possession.possessive`, `Turkish.Possession.locative`: the possessive and the
  locative existential sentences

## Main results

* `Turkish.Possession.ayten`, `paramız`, `murat`, `bende`: the grammar's examples
* `Turkish.Possession.sizin`: the possessee's head is never bare

## Implementation notes

A noun phrase is a list of words whose last word, the head, takes the suffixes. The possessor
is regular, so the irregular genitives of the first-person pronouns (*benim*, *bizim*) are not
derived. The predicate carries no person marker, the subject being third person.

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
-/

@[expose] public section

open Phonology Turkish Turkish.Phonology Turkish.Nominal

namespace Turkish.Possession

/-- *var* 'present, existent'. -/
def var : List Segment := [v, a, r]

/-- *yok* 'absent, non-existent'. -/
def yok : List Segment := [y, o, k]

/-- An existential with its copular marker, which a present tense unmarked for aspect or
modality lacks. -/
def predicate (e : List Segment) (cop : Option (Verb.Exponent .copula)) : List Segment :=
  realize e (cop.toList.map Verb.Exponent.form)

/-- A noun phrase with a suffix on its head, the last word. -/
def inflect (np : List (List Segment)) (sfx : Suffix) : List (List Segment) :=
  np.dropLast ++ (np.getLast?.map (realize · [sfx])).toList

/-- The possessive existential sentences of a possessor `pr`, adverbials `adv`, a possessee
`pe` whose head takes the possessive suffix of the possessor's cell `c`, and a predicate. The
possessor may be empty, and the adverbials precede or follow it. -/
def possessive (pr adv pe : List (List Segment)) (c : Agreement.Bundle) (pred : List Segment) :
    List (List (List Segment)) :=
  let pr := inflect pr Exponent.genitive.form
  let pe := inflect pe (Exponent.possessive c).form ++ [pred]
  [pr ++ adv ++ pe, adv ++ pr ++ pe]

/-- The locative existential sentence of a location `pr` denoting a person or an institution, a
possessee `pe` and a predicate. -/
def locative (pr pe : List (List Segment)) (pred : List Segment) : List (List Segment) :=
  inflect pr Exponent.locative.form ++ pe ++ [pred]

/-- *Ayten-in İstanbul'da iki arkadaş-ı var* and *İstanbul'da Ayten-in iki arkadaş-ı var*
'Ayten has two friends in Istanbul' (§12.1.1.2 (21)). -/
theorem ayten :
    possessive [[a, y, t, e, n]] (inflect [[i, s, t, a, n, b, u, l]] Exponent.locative.form)
        [[i, k, i], [a, r, k, a, d, a, ş]] (.personNumber .third .singular) var =
      [[[a, y, t, e, n, i, n], [i, s, t, a, n, b, u, l, d, a], [i, k, i],
          [a, r, k, a, d, a, ş, ı], [v, a, r]],
        [[i, s, t, a, n, b, u, l, d, a], [a, y, t, e, n, i, n], [i, k, i],
          [a, r, k, a, d, a, ş, ı], [v, a, r]]] := by
  decide

/-- *O gün paramız yoktu* 'We had no money that day' (§12.1.1.2 (22)). -/
theorem paramız :
    [[o], [g, ü, n], [p, a, r, a, m, ı, z], [y, o, k, t, u]] ∈
      possessive [] [[o], [g, ü, n]] [[p, a, r, a]] (.personNumber .first .plural)
        (predicate yok (some .pastCopula)) := by
  decide

/-- *Murat'ın yatı var* 'Murat has a yacht' (§12.1.1.2 (26)). -/
theorem murat :
    [[m, u, r, a, t, ı, n], [y, a, t, ı], [v, a, r]] ∈
      possessive [[m, u, r, a, t]] [] [[y, a, t]] (.personNumber .third .singular) var := by
  decide

/-- *Bende bir kitap var* 'I have a book' (§12.1.1.2 (17)). -/
theorem bende :
    locative [[b, e, n]] [[b, i, r], [k, i, t, a, p]] var =
      [[b, e, n, d, e], [b, i, r], [k, i, t, a, p], [v, a, r]] := by
  decide

/-- The possessive suffix on the possessee's head is obligatory in a possessive existential
sentence, unlike in a genitive-possessive noun phrase (§14.4 (117), without its question
particle): *Siz-in araba-nız var* 'You have a car', but no cell gives *Sizin araba var*. -/
theorem sizin :
    [[s, i, z, i, n], [a, r, a, b, a, n, ı, z], [v, a, r]] ∈
        possessive [[s, i, z]] [] [[a, r, a, b, a]] (.personNumber .second .plural) var ∧
      ∀ c ∈ Agreement.Bundle.personNumberCells,
        [[s, i, z, i, n], [a, r, a, b, a], [v, a, r]] ∉
          possessive [[s, i, z]] [] [[a, r, a, b, a]] c var := by
  decide

end Turkish.Possession
