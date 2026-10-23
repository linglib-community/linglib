module

public import Linglib.Fragments.Finnish.Case
public import Linglib.Fragments.Finnish.Phonology

/-!
# Finnish case endings

The endings of the Finnish cases in the singular, as Karlsson's table of cases gives them, in
his archiphonemic spelling: the suffix vowel `A` alternates by palatal harmony and the copy
vowel `V` repeats the nearest vowel before it. A case has one ending after a stem in a short
vowel, as in *auto-ssa* 'in a car' and *auto-on* 'into a car', and the partitive and the
illative have alternants that the shape of the stem selects: the partitive -tA and -ttA, as in
*vet-tä* 'water' and *perhe-ttä* 'family', and the illative -hVn and -seen, as in *maa-han*
'into the country' and *Porvoo-seen* 'to Porvoo'. The same endings follow the infinitives
(`Finnish.Infinitive`).

## Main definitions

* `Finnish.Declension.endings`: the endings of each case, the ending after a short vowel first.
* `Finnish.Declension.ending`: the ending of a case after a stem in a short vowel.

## Main results

* `Finnish.Declension.isSome_ending`: every case has an ending.

## Implementation notes

Which alternant a stem takes is not represented. The endings after the plural and before a
possessive ending are in `Finnish.Nominal`.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Finnish.Declension

open Phonology

/-- The endings of each case, the ending after a stem in a short vowel first. -/
def endings : Case → List (List Segment)
  | .nom => [[]]
  | .gen => [[n]]
  | .acc => [[t]]
  | .part => [[A], [t, A], [t, t, A]]
  | .ine => [[s, s, A]]
  | .ela => [[s, t, A]]
  | .ill => [[V, n], [h, V, n], [s, e, e, n]]
  | .ade => [[l, l, A]]
  | .abl => [[l, t, A]]
  | .all => [[l, l, e]]
  | .ess => [[n, A]]
  | .transl => [[k, s, i]]
  | .com => [[i, n, e]]
  | .abess => [[t, t, A]]
  | .instr => [[n]]

/-- The ending of a case after a stem in a short vowel. -/
def ending (c : Case) : Option (List Segment) := (endings c).head?

/-- Every case has an ending. -/
theorem isSome_ending (c : Case) : (ending c).isSome := by
  cases c <;> decide

end Finnish.Declension
