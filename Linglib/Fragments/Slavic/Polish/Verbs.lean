module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Category.Verb.Defs

/-!
# Polish verbs

Verbal prefixes and simplex verbs of Polish, the material of the studies of verbal prefixation
listed below. A prefix is a morph with its form only: the position a prefix occupies in a word is
a study's analysis. A verb records its citation form, the infinitive, and its lexical aspect at
the dictionary value: the simplex verbs are imperfective except the semelfactives in *-nąć*. The
Vendler class is recorded for the semelfactives and the statives.

## Implementation notes

* A citation form is a single root morph. The division of verbs into conjugation classes is a
  point of contention, and a study that assigns classes assigns them to these entries.
* *s-* is the spelling of the prefix *z-* before a voiceless consonant; the two are separate
  morphs, since nothing yet models the alternation.

## References

* [jablonska-2004]
* [svenonius-2004]
-/

@[expose] public section

namespace Polish.Verbs

open Morphology

/-! ### Prefixes -/

/-- The prefix *po-*. -/
def po : Morph := .pref "po"

/-- The prefix *za-*. -/
def za : Morph := .pref "za"

/-- The prefix *w-* 'in'. -/
def w : Morph := .pref "w"

/-- The prefix *prze-* 'through'. -/
def prze : Morph := .pref "prze"

/-- The prefix *ob-* 'around'. -/
def ob : Morph := .pref "ob"

/-- The prefix *wy-* 'out'. -/
def wy : Morph := .pref "wy"

/-- The prefix *pod-* 'under'. -/
def pod : Morph := .pref "pod"

/-- The prefix *do-* 'to'. -/
def do_ : Morph := .pref "do"

/-- The prefix *z-*. -/
def z : Morph := .pref "z"

/-- The prefix *s-*, the spelling of *z-* before a voiceless consonant. -/
def s : Morph := .pref "s"

/-! ### Statives -/

/-- *siedzieć* 'sit'. -/
def siedziec : Verb where
  morphs := [.root "siedzieć"]
  vendlerClass := some .state
  perfectivity := some .imperfective

/-- *kochać* 'love'. -/
def kochac : Verb where
  morphs := [.root "kochać"]
  vendlerClass := some .state
  perfectivity := some .imperfective

/-- *lubić* 'like'. -/
def lubic : Verb where
  morphs := [.root "lubić"]
  vendlerClass := some .state
  perfectivity := some .imperfective

/-! ### Verbs of becoming in *-eć* -/

/-- *jaśnieć* 'be bright', from *jasny* 'bright'. -/
def jasniec : Verb where
  morphs := [.root "jaśnieć"]
  perfectivity := some .imperfective

/-- *siwieć* 'turn grey', from *siwy* 'grey'. -/
def siwiec : Verb where
  morphs := [.root "siwieć"]
  perfectivity := some .imperfective

/-- *ciemnieć* 'get dark', from *ciemny* 'dark'. -/
def ciemniec : Verb where
  morphs := [.root "ciemnieć"]
  perfectivity := some .imperfective

/-- *drożeć* 'get expensive', from *drogi* 'expensive'. -/
def drozec : Verb where
  morphs := [.root "drożeć"]
  perfectivity := some .imperfective

/-- *babieć* 'become effeminate'. -/
def babiec : Verb where
  morphs := [.root "babieć"]
  perfectivity := some .imperfective

/-- *smutnieć* 'get sad', from *smutny* 'sad'. -/
def smutniec : Verb where
  morphs := [.root "smutnieć"]
  perfectivity := some .imperfective

/-- *dziczeć* 'go wild', from *dziki* 'wild'. -/
def dziczec : Verb where
  morphs := [.root "dziczeć"]
  perfectivity := some .imperfective

/-! ### Inchoatives in *-nąć* -/

/-- *marznąć* 'freeze'. -/
def marznac : Verb where
  morphs := [.root "marznąć"]
  perfectivity := some .imperfective

/-- *głuchnąć* 'go deaf'. -/
def gluchnac : Verb where
  morphs := [.root "głuchnąć"]
  perfectivity := some .imperfective

/-- *więdnąć* 'wither'. -/
def wiednac : Verb where
  morphs := [.root "więdnąć"]
  perfectivity := some .imperfective

/-- *ślepnąć* 'go blind'. -/
def slepnac : Verb where
  morphs := [.root "ślepnąć"]
  perfectivity := some .imperfective

/-- *gasnąć* 'go out'. -/
def gasnac : Verb where
  morphs := [.root "gasnąć"]
  perfectivity := some .imperfective

/-! ### Semelfactives in *-nąć* -/

/-- *warknąć* 'snarl once'. -/
def warknac : Verb where
  morphs := [.root "warknąć"]
  vendlerClass := some .semelfactive
  perfectivity := some .perfective

/-- *kopnąć* 'kick once'. -/
def kopnac : Verb where
  morphs := [.root "kopnąć"]
  vendlerClass := some .semelfactive
  perfectivity := some .perfective

/-- *machnąć* 'wave once'. -/
def machnac : Verb where
  morphs := [.root "machnąć"]
  vendlerClass := some .semelfactive
  perfectivity := some .perfective

/-- *miauknąć* 'meow once'. -/
def miauknac : Verb where
  morphs := [.root "miauknąć"]
  vendlerClass := some .semelfactive
  perfectivity := some .perfective

/-- *szepnąć* 'whisper once'. -/
def szepnac : Verb where
  morphs := [.root "szepnąć"]
  vendlerClass := some .semelfactive
  perfectivity := some .perfective

/-! ### Other simplex verbs -/

/-- *czytać* 'read'. -/
def czytac : Verb where
  morphs := [.root "czytać"]
  perfectivity := some .imperfective

/-- *grać* 'play'. -/
def grac : Verb where
  morphs := [.root "grać"]
  perfectivity := some .imperfective

/-- *palić* 'smoke, burn'. -/
def palic : Verb where
  morphs := [.root "palić"]
  perfectivity := some .imperfective

/-- *chować* 'hide'. -/
def chowac : Verb where
  morphs := [.root "chować"]
  perfectivity := some .imperfective

/-- *pisać* 'write'. -/
def pisac : Verb where
  morphs := [.root "pisać"]
  perfectivity := some .imperfective

/-- *śpiewać* 'sing'. -/
def spiewac : Verb where
  morphs := [.root "śpiewać"]
  perfectivity := some .imperfective

/-- *kopać* 'dig'. -/
def kopac : Verb where
  morphs := [.root "kopać"]
  perfectivity := some .imperfective

/-- *dmuchać* 'blow'. -/
def dmuchac : Verb where
  morphs := [.root "dmuchać"]
  perfectivity := some .imperfective

/-- *machać* 'wave', the verb of repeated waving beside the semelfactive *machnąć*. -/
def machac : Verb where
  morphs := [.root "machać"]
  perfectivity := some .imperfective

/-- *szeptać* 'whisper', the verb of continued whispering beside the semelfactive *szepnąć*. -/
def szeptac : Verb where
  morphs := [.root "szeptać"]
  perfectivity := some .imperfective

/-- *tracić* 'lose'. -/
def tracic : Verb where
  morphs := [.root "tracić"]
  perfectivity := some .imperfective

/-- *robić* 'make, do'. -/
def robic : Verb where
  morphs := [.root "robić"]
  perfectivity := some .imperfective

/-- *brudzić* 'dirty'. -/
def brudzic : Verb where
  morphs := [.root "brudzić"]
  perfectivity := some .imperfective

/-- *bić* 'beat'. -/
def bic : Verb where
  morphs := [.root "bić"]
  perfectivity := some .imperfective

/-- *chwalić* 'praise'. -/
def chwalic : Verb where
  morphs := [.root "chwalić"]
  perfectivity := some .imperfective

/-- *równać* 'level'. -/
def rownac : Verb where
  morphs := [.root "równać"]
  perfectivity := some .imperfective

/-- *twierdzić* 'claim'. -/
def twierdzic : Verb where
  morphs := [.root "twierdzić"]
  perfectivity := some .imperfective

/-! ### Verbs of motion

Each verb of motion has a directed (determinate) and a non-directed (indeterminate) member. -/

/-- *iść* 'go', directed. -/
def isc : Verb where
  morphs := [.root "iść"]
  perfectivity := some .imperfective

/-- *biec* 'run', directed. -/
def biec : Verb where
  morphs := [.root "biec"]
  perfectivity := some .imperfective

/-- *lecieć* 'fly', directed. -/
def leciec : Verb where
  morphs := [.root "lecieć"]
  perfectivity := some .imperfective

/-- *ciągnąć* 'drag', directed. -/
def ciagnac : Verb where
  morphs := [.root "ciągnąć"]
  perfectivity := some .imperfective

/-- *płynąć* 'swim', directed. -/
def plynac : Verb where
  morphs := [.root "płynąć"]
  perfectivity := some .imperfective

/-- *chodzić* 'walk', the non-directed member of *iść*. -/
def chodzic : Verb where
  morphs := [.root "chodzić"]
  perfectivity := some .imperfective

/-- *biegać* 'run', non-directed. -/
def biegac : Verb where
  morphs := [.root "biegać"]
  perfectivity := some .imperfective

/-- *latać* 'fly', non-directed. -/
def latac : Verb where
  morphs := [.root "latać"]
  perfectivity := some .imperfective

/-- *ciągać* 'drag', non-directed. -/
def ciagac : Verb where
  morphs := [.root "ciągać"]
  perfectivity := some .imperfective

/-- *pływać* 'swim', non-directed. -/
def plywac : Verb where
  morphs := [.root "pływać"]
  perfectivity := some .imperfective

end Polish.Verbs
