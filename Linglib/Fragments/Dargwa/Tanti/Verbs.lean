module

public import Linglib.Fragments.Dargwa.Tanti.Locatives
public import Linglib.Morphology.Morphotactics.AffixTemplate

/-!
# Tanti Dargwa verbs

A Tanti Dargwa verb is simplex (a root with at most a gender prefix), a preverb verb, or complex
(a lexical stem followed by a light verb, with any preverbs between them). Roots, some preverbs and
some lexical stems agree in gender by a prefix, so each is given as its morphs under each gender
marker, and the marker of the agreement controller fills every gender slot of a verb. The preverbs
share the orientation markers and directions of the locative forms.

## Main definitions

* `Dargwa.Tanti.Localization.preverb?`, `Dargwa.Tanti.Direction.preverb`: the preverbs of a
  localization with an orientation, and of a direction
* `Dargwa.Tanti.localizationPreverbs`, `Dargwa.Tanti.directionPreverbs`: the two groups of preverbs
* `Dargwa.Tanti.preverbTemplate`: the positions of the two groups, the first before the second
* `Dargwa.Tanti.lightVerbs`, `Dargwa.Tanti.boundLightVerbs`: the light verbs, and those found only
  in complex verbs
* `Dargwa.Tanti.ComplexVerb`, `Dargwa.Tanti.ComplexVerb.morphs`: a complex verb and its morphs

## Main results

* `Dargwa.Tanti.Localization.preverb?_super`: *če-*, *če-b-* and *če-r-* are *super* with the
  lative, essive and elative markers
* `Dargwa.Tanti.length_le_two_of_licensed`: a verb whose preverbs the template licenses has at
  most two
* `Dargwa.Tanti.morphs_startCrying`: the stem and the light verb of *w-isːe-w-ig-* take the same
  marker

## Implementation notes

* Sumbatova gives the orientations of the first group as the lative, essive and elative, and
  glosses *če-tːi-* and *gu-tːi-* 'above (motion)' and 'below (motion)'; they are *super* and
  *sub* with the translative marker. *tːura-* 'outside', *ča-* 'upward' and *ča-r-* 'from the
  top' are cited whole.
* Sumbatova lists *aq-* both as 'hang' and among the light verbs found only in complex verbs, so
  `hang` is in both inventories.
* Her list of light verbs omits *b-ut'-* 'cut', the light verb of *č'u-b-ut'-* 'divide by two'.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
-/

@[expose] public section

namespace Dargwa.Tanti

open Morphology

/-! ### Preverbs -/

/-- The prefix of a localization in a preverb of the first group: *če-* 'on' for *super*, *gu-*
'under' for *sub*, *sa-* 'in front of' for *ante*, and none for the others. -/
def Localization.prefix? : Localization → Option Morph
  | .super => some (.pref "če")
  | .sub => some (.pref "gu")
  | .ante => some (.pref "sa")
  | _ => none

/-- The preverb of the first group with the localization `l` and the orientation `o`, the prefix
of `l` followed by the marker of `o`, and none for a localization without a prefix. -/
def Localization.preverb? (l : Localization) (o : Orientation) :
    Option (Gender.Marker → List Morph) :=
  l.prefix?.map fun p g ↦ p :: ((o.marker? g).map Morph.pref).toList

/-- *tːura-* 'outside', a lative. -/
def outside : Gender.Marker → List Morph := fun _ ↦ [.pref "tːura"]

/-- *ča-* 'upward', from *če-* 'on' and *ha-* 'upward'. -/
def onUpward : Gender.Marker → List Morph := fun _ ↦ [.pref "ča"]

/-- *ča-r-* 'from the top'. -/
def fromTop : Gender.Marker → List Morph := fun _ ↦ [.pref "ča", .pref "r"]

/-- The preverbs of the first group, which express a localization and an orientation: the
lative, essive and elative of each localization with a prefix, *če-tːi-* 'above (motion)' and
*gu-tːi-* 'below (motion)', and those cited whole. -/
def localizationPreverbs : Finset (Gender.Marker → List Morph) :=
  ((Finset.univ ×ˢ {.lative, .essive, .elative} ∪ {(.super, .translative), (.sub, .translative)} :
      Finset (Localization × Orientation)).biUnion fun (l, o) ↦ (l.preverb? o).toFinset) ∪
    {outside, onUpward, fromTop}

/-- The preverb of a direction: *ha-* 'upward', *ka-* 'downward', *sa-* 'hither (to the
speaker)' and *b-it-* 'thither'. -/
def Direction.preverb : Direction → Gender.Marker → List Morph
  | .up, _ => [.pref "ha"]
  | .down, _ => [.pref "ka"]
  | .hither, _ => [.pref "sa"]
  | .thither, g => [.pref g.form, .pref "it"]

/-- *le-* 'hither (to the addressee)', a direction the locative forms lack. -/
def toAddressee : Gender.Marker → List Morph := fun _ ↦ [.pref "le"]

/-- The preverbs of the second group, which express a direction. -/
def directionPreverbs : Finset (Gender.Marker → List Morph) :=
  insert toAddressee (Finset.univ.image Direction.preverb)

/-- The two groups of preverbs, the positions they fill. -/
inductive PreverbGroup where
  /-- The first group, which expresses a localization and an orientation. -/
  | localization
  /-- The second group, which expresses a direction. -/
  | direction
  deriving DecidableEq, Repr, Fintype

/-- The preverbs of a group. -/
def PreverbGroup.preverbs : PreverbGroup → Finset (Gender.Marker → List Morph)
  | .localization => localizationPreverbs
  | .direction => directionPreverbs

/-- As a rule a verb has at most two preverbs, one of the first group followed by one of the
second. -/
def preverbTemplate : AffixTemplate PreverbGroup where
  prefixSlots := [.localization, .direction]

/-- The template licenses a string of preverbs exactly when it has at most one of each group, the
first group's before the second's. -/
theorem licensed_preverbTemplate_iff {E : PreverbGroup → Type*} {w : List (Σ σ, E σ)} :
    preverbTemplate.Licensed w ↔ (w.map Sigma.fst).Sublist [.localization, .direction] :=
  AffixTemplate.mem_language_iff_sublist rfl

/-- A string of preverbs the template licenses has at most two. -/
theorem length_le_two_of_licensed {E : PreverbGroup → Type*} {w : List (Σ σ, E σ)}
    (h : preverbTemplate.Licensed w) : w.length ≤ 2 := by
  simpa using (licensed_preverbTemplate_iff.1 h).length_le

/-- *če-*, *če-b-* and *če-r-* are *super* with the lative, essive and elative markers. -/
theorem Localization.preverb?_super :
    Localization.super.preverb? .lative = some (fun _ ↦ [.pref "če"]) ∧
      Localization.super.preverb? .essive = some (fun g ↦ [.pref "če", .pref g.form]) ∧
      Localization.super.preverb? .elative = some (fun _ ↦ [.pref "če", .pref "r"]) :=
  ⟨rfl, rfl, rfl⟩

/-! ### Light verbs -/

/-- *b-arq'-* 'do, make', the most common light verb. -/
def make : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "arq'"]

/-- *b-iχ-* 'become'. -/
def become : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "iχ"]

/-- *w-ik'-* 'speak'. -/
def speak : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "ik'"]

/-- *b-at-* 'leave'. -/
def leave : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "at"]

/-- *b-ič-* 'fall'. -/
def fall : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "ič"]

/-- *b-aˁq-* 'hit'. -/
def hit : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "aˁq"]

/-- *b-icː-* 'stand up'. -/
def standUp : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "icː"]

/-- *b-ig-* 'sit down'. -/
def sitDown : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "ig"]

/-- *aq-* 'hang'. -/
def hang : Gender.Marker → List Morph := fun _ ↦ [.root "aq"]

/-- *aʁ-* 'reach'. -/
def reach : Gender.Marker → List Morph := fun _ ↦ [.root "aʁ"]

/-- *b-ač'-* 'come'. -/
def come : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "ač'"]

/-- *le-b-q'-* 'come (here)', whose gender prefix follows the preverb *le-*. -/
def comeHere : Gender.Marker → List Morph := fun g ↦ toAddressee g ++ [.pref g.form, .root "q'"]

/-- *b-arʁ-* 'collect'. -/
def collect : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "arʁ"]

/-- *b-ixː-* 'put'. -/
def put : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "ixː"]

/-- *it-* 'beat'. -/
def beat : Gender.Marker → List Morph := fun _ ↦ [.root "it"]

/-- *ag-* 'go away'. -/
def goAway : Gender.Marker → List Morph := fun _ ↦ [.root "ag"]

/-- *ʔ-* 'say'. -/
def say : Gender.Marker → List Morph := fun _ ↦ [.root "ʔ"]

/-- *b-erk'-* 'drive'. -/
def drive : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "erk'"]

/-- *arg-* 'sift'. -/
def sift : Gender.Marker → List Morph := fun _ ↦ [.root "arg"]

/-- *b-ertː-* 'tear'. -/
def tear : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "ertː"]

/-- *b-aˁʜ-* 'struggle'. -/
def struggle : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "aˁʜ"]

/-- *b-ut'-* 'cut'. -/
def cut : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "ut'"]

/-- *b-uq-*, found only in complex verbs. -/
def uq : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "uq"]

/-- *b-ikː-*, found only in complex verbs. -/
def ikk : Gender.Marker → List Morph := fun g ↦ [.pref g.form, .root "ikː"]

/-- *art-*, found only in complex verbs. -/
def art : Gender.Marker → List Morph := fun _ ↦ [.root "art"]

/-- The light verbs Sumbatova lists. -/
def lightVerbs : Finset (Gender.Marker → List Morph) :=
  {make, become, speak, leave, fall, hit, standUp, sitDown, hang, reach, come, comeHere, collect,
    put, beat, goAway, say, drive, sift, tear, struggle}

/-- The light verbs Sumbatova lists as found only in complex verbs. -/
def boundLightVerbs : Finset (Gender.Marker → List Morph) := {uq, hang, ikk, art}

/-! ### Complex verbs -/

/-- The word class of the lexical stem of a complex verb as an independent word. -/
inductive StemClass where
  | noun
  | adjective
  | numeral
  | verb
  | ideophone
  deriving DecidableEq, Repr, Fintype

/-- A complex verb is a lexical stem followed by a light verb, with any preverbs between them. -/
structure ComplexVerb where
  /-- The lexical stem, which carries the core meaning of the complex. -/
  stem : Gender.Marker → List Morph
  /-- The word class of the stem, `none` for a stem restricted to the complex verb. -/
  category : Option StemClass
  /-- The preverbs between the stem and the light verb, each with its group. -/
  preverbs : List (Σ σ : PreverbGroup, σ.preverbs) := []
  /-- The light verb. -/
  lightVerb : Gender.Marker → List Morph
  /-- The meaning of the complex verb. -/
  gloss : String

/-- The morphs of a complex verb whose agreement controller takes the marker `g`. -/
def ComplexVerb.morphs (c : ComplexVerb) (g : Gender.Marker) : List Morph :=
  c.stem g ++ c.preverbs.flatMap (·.2.1 g) ++ c.lightVerb g

/-- *taman-b-arq'-* 'finish' (transitive), from *taman* 'end'. -/
def finish : ComplexVerb :=
  { stem := fun _ ↦ [.root "taman"], category := some .noun, lightVerb := make,
    gloss := "finish" }

/-- *ʜaˁdur-d-arq'-* 'prepare', from *ʜaˁdur-* 'ready'. -/
def prepare : ComplexVerb :=
  { stem := fun _ ↦ [.root "ʜaˁdur"], category := some .adjective, lightVerb := make,
    gloss := "prepare" }

/-- *č'u-b-ut'-* 'divide by two', from *č'u* 'two'. -/
def divideByTwo : ComplexVerb :=
  { stem := fun _ ↦ [.root "č'u"], category := some .numeral, lightVerb := cut,
    gloss := "divide by two" }

/-- *qeʜ-w-ik'-* 'cough' (imperfective), from the ideophone *qeʜ-*. -/
def cough : ComplexVerb :=
  { stem := fun _ ↦ [.root "qeʜ"], category := some .ideophone, lightVerb := speak,
    gloss := "cough" }

/-- *w-isːe-w-ig-* 'start crying', from *w-isː-* 'cry' (imperfective). -/
def startCrying : ComplexVerb :=
  { stem := fun g ↦ [.pref g.form, .root "isːe"], category := some .verb, lightVerb := sitDown,
    gloss := "start crying" }

/-- *tːurχ-b-arq'-* 'spin', from a stem found nowhere else. -/
def spin : ComplexVerb :=
  { stem := fun _ ↦ [.root "tːurχ"], category := none, lightVerb := make, gloss := "spin" }

/-- *t'aš-ka-b-icː-* 'stop', from a stem found nowhere else, with the preverb *ka-* 'downward'
between it and the light verb. -/
def stop : ComplexVerb :=
  { stem := fun _ ↦ [.root "t'aš"], category := none,
    preverbs := [⟨.direction, Direction.down.preverb, by decide⟩], lightVerb := standUp,
    gloss := "stop" }

/-- In *w-isːe-w-ig-* 'start crying' the stem and the light verb each take the marker of the
agreement controller. -/
theorem morphs_startCrying (g : Gender.Marker) :
    startCrying.morphs g = [.pref g.form, .root "isːe", .pref g.form, .root "ig"] := rfl

end Dargwa.Tanti
