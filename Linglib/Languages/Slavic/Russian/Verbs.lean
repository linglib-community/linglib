module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Verb.Defs

/-!
# Russian verbs

Verbal prefixes and verbs of Russian, the material of the study of verbal prefixation listed
below. A prefix is a morph with its form only: the position a prefix occupies in a word is a
study's analysis. A verb records its citation form, the infinitive, and its lexical aspect at the
dictionary value. The transliteration is the study's, with *j* for palatalization, as in
*brositj*.

## References

* [svenonius-2004]
-/

@[expose] public section

namespace Russian.Verbs

open Morphology

/-! ### Prefixes -/

/-- The prefix *za-*. -/
def za : Morph := .pref "za"

/-- The prefix *vy-* 'out'. -/
def vy : Morph := .pref "vy"

/-- The prefix *po-*. -/
def po : Morph := .pref "po"

/-! ### Verbs -/

/-- *brositj* 'throw'. -/
def brosit : Verb where
  morphs := [.root "brositj"]
  perfectivity := some .perfective

/-- *brosatj* 'throw'. -/
def brosat : Verb where
  morphs := [.root "brosatj"]
  perfectivity := some .imperfective

/-- *-brasyvatj* 'throw', the secondary imperfective stem of *brositj*, which occurs prefixed, as
in *vy-brasyvatj* 'throw out'. -/
def brasyvat : Verb where
  morphs := [.root "brasyvatj"]
  perfectivity := some .imperfective

/-- *kuritj* 'smoke'. -/
def kurit : Verb where
  morphs := [.root "kuritj"]
  perfectivity := some .imperfective

/-- *čitatj* 'read'. -/
def chitat : Verb where
  morphs := [.root "čitatj"]
  perfectivity := some .imperfective

end Russian.Verbs
