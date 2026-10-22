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
* `Turkish.Possession.inflect`: a noun phrase with a suffix on its head
* `Turkish.Possession.IsPossessive`, `Turkish.Possession.locative`: the possessive and the
  locative existential sentences

## Main results

* `Turkish.Possession.IsPossessive.ne_bare`: the head of the possessee is never bare

## Implementation notes

A noun phrase is a list of words whose last word, the head, takes the suffixes. The possessor
is regular, so the irregular genitives of the first-person pronouns (*benim*, *bizim*) are not
derived. The predicate carries no person marker, the subject being third person. The
grammar's examples are derived in `Studies/GokselKerslake2005.lean`.

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

@[simp] theorem inflect_nil (sfx : Suffix) : inflect [] sfx = [] := rfl

@[simp] theorem inflect_concat (np : List (List Segment)) (w : List Segment) (sfx : Suffix) :
    inflect (np ++ [w]) sfx = np ++ [realize w [sfx]] := by
  simp [inflect]

variable (pr adv pe : List (List Segment)) (c : Agreement.Bundle) (pred : List Segment)

/-- `s` is a possessive existential sentence of a possessor `pr`, adverbials `adv`, a possessee
`pe` whose head takes the possessive suffix of the possessor's cell `c`, and a predicate. The
possessor may be empty, and the adverbials precede or follow it. -/
def IsPossessive (s : List (List Segment)) : Prop :=
  let gen := inflect pr Exponent.genitive.form
  let rest := inflect pe (Exponent.possessive c).form ++ [pred]
  s = gen ++ adv ++ rest ∨ s = adv ++ gen ++ rest

instance : DecidablePred (IsPossessive pr adv pe c pred) := fun _ ↦
  inferInstanceAs (Decidable (_ ∨ _))

/-- The locative existential sentence of a location `pr` denoting a person or an institution, a
possessee `pe` and a predicate. -/
def locative : List (List Segment) :=
  inflect pr Exponent.locative.form ++ pe ++ [pred]

variable {pr adv c pred}

/-- The head of the possessee is never bare: for every person-number cell, no possessive
existential sentence ends in the bare head and the predicate. -/
theorem IsPossessive.ne_bare (hc : c ∈ Agreement.Bundle.personNumberCells)
    {np s : List (List Segment)} {w : List Segment}
    (hs : IsPossessive pr adv (np ++ [w]) c pred s) (xs : List (List Segment)) :
    s ≠ xs ++ [w, pred] := by
  have hcells : ∀ c ∈ Agreement.Bundle.personNumberCells,
      (Exponent.possessive c).form.segments ≠ [] := by decide
  have hw := realize_singleton_ne_self (hcells c hc) w
  rintro rfl
  rcases hs with h | h <;>
  · exact hw (by simpa using (congrArg (·.reverse.tail.head?) h).symm)

end Turkish.Possession
