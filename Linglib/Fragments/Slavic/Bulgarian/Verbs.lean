module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Verb.Defs

/-!
# Bulgarian verbs

Verbal prefixes and verbs of Bulgarian, the material of the study of multiple prefixation listed
below. A prefix is a morph with its form only. A verb records its citation form, the first person
singular present, Bulgarian having no infinitive, and its lexical aspect at the dictionary value.
The study's reclassification of the simplex imperfectives as aspectless, like its classification
of prefix occurrences, belongs to the study.

## References

* [istratkova-2004]
-/

@[expose] public section

namespace Bulgarian.Verbs

open Morphology

/-! ### Prefixes -/

/-- The prefix *za-*. -/
def za : Morph := .pref "za"

/-- The prefix *iz-*. -/
def iz : Morph := .pref "iz"

/-- The prefix *po-*. -/
def po : Morph := .pref "po"

/-- The prefix *pro-*. -/
def pro : Morph := .pref "pro"

/-- The prefix *na-*. -/
def na : Morph := .pref "na"

/-- The prefix *pre-*. -/
def pre : Morph := .pref "pre"

/-- The prefix *raz-*. -/
def raz : Morph := .pref "raz"

/-- The prefix *do-*. -/
def do_ : Morph := .pref "do"

/-! ### Verbs -/

/-- *piša* 'write'. -/
def pisha : Verb where
  morphs := [.root "piša"]
  perfectivity := some .imperfective

/-- *misl'a* 'think'. -/
def misla : Verb where
  morphs := [.root "misl'a"]
  perfectivity := some .imperfective

/-- *znam* 'know'. -/
def znam : Verb where
  morphs := [.root "znam"]
  perfectivity := some .imperfective

/-- *blest'a* 'glitter'. -/
def blesta : Verb where
  morphs := [.root "blest'a"]
  perfectivity := some .imperfective

/-- *običam* 'love'. -/
def obicham : Verb where
  morphs := [.root "običam"]
  perfectivity := some .imperfective

/-- *četa* 'read'. -/
def cheta : Verb where
  morphs := [.root "četa"]
  perfectivity := some .imperfective

/-- *razkaža* 'narrate', historically *raz-kaža* 'around-say'. -/
def razkazha : Verb where
  morphs := [.root "razkaža"]
  perfectivity := some .perfective

/-- *dam* 'give', the base of *pro-dam* 'sell'. -/
def dam : Verb where
  morphs := [.root "dam"]
  perfectivity := some .perfective

/-- *kaža* 'tell, say', the base of *raz-kaža* 'narrate'. -/
def kazha : Verb where
  morphs := [.root "kaža"]
  perfectivity := some .perfective

/-- *kup'a* 'buy'. -/
def kupja : Verb where
  morphs := [.root "kup'a"]
  perfectivity := some .perfective

/-- *peja* 'sing'. -/
def peja : Verb where
  morphs := [.root "peja"]
  perfectivity := some .imperfective

/-- *reža* 'cut'. -/
def rezha : Verb where
  morphs := [.root "reža"]
  perfectivity := some .imperfective

end Bulgarian.Verbs
