module

public import Linglib.Fragments.Bantu.Params
public import Linglib.Syntax.Agreement.Paradigm

/-!
# Setswana subject markers

This file defines the subject markers of the Setswana verb that the glossed examples of
[storment-2026] attest: in the present, those of classes 1, 2, 10 and 17 and of the speech-act
participants, and in the past, those of classes 1 and 17. Class 17 *go* is also the marker of
expletive, locative and infinitival subjects ((54)–(57)).

## Implementation notes

* The paper glosses the homophonous markers of classes 15 and 17 all as class 17 (fn. 2).
* The class 1 marker of a dependent verb, *a* in (11), (76) and (83a), is not recorded.

## TODO

* The markers of the other classes and of the second person plural, from a grammar.

## References

* [storment-2026]
-/

@[expose] public section

namespace Setswana

open Agreement Bantu

/-- The present subject marker of a class. -/
def subjPrefix : NounClass → Option String
  | .cl1 => some "o"    -- (76), (83a)
  | .cl2 => some "ba"   -- (72)
  | .cl10 => some "di"  -- (35), (75)
  | .cl17 => some "go"  -- (36), (38), (54)
  | _ => none

/-- The past subject marker of a class. -/
def pastSubjPrefix : NounClass → Option String
  | .cl1 => some "a"    -- (6), (65)
  | .cl17 => some "ga"  -- (4), (55)
  | _ => none

/-- The present subject markers of the person cells: *ke*, *o* and *re* for the speech-act
participants, (37), (74) and (70), and those of classes 1 and 2 for the third person. -/
def subjectPrefix : Paradigm String :=
  [(.personNumber .first .singular, "ke"), (.personNumber .second .singular, "o"),
    (.personNumber .third .singular, (subjPrefix .cl1).get rfl),
    (.personNumber .first .plural, "re"),
    (.personNumber .third .plural, (subjPrefix .cl2).get rfl)]

end Setswana
