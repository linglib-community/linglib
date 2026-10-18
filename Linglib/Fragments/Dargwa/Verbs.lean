module

public import Linglib.Morphology.Morph

/-!
# Tanti Dargwa verbs

This file defines the light verbs and complex verbs of Tanti Dargwa as Sumbatova describes
them. A Dargwa verb is simplex, a bare root with at most a gender prefix, a preverb verb, or a
complex verb, a lexical stem followed by a light verb with any preverbs between them. The
lexical stems are noun, adjective, numeral, verb or ideophone stems, some of them found only in
the complex verb, and a few light verbs likewise occur only there. The valency alternations of
the verb are in `Voice.lean`.

## Main definitions

* `Dargwa.LightVerb`, `Dargwa.lightVerbs`: the light verbs, each with the meaning of the
  homophonous simplex verb where it has one
* `Dargwa.ComplexVerb`: a lexical stem, cited as its root, with its word class, preverbs and
  light verb

## Implementation notes

* A light verb is cited by its stem without the gender prefix, `agrees` recording the roots
  whose shape begins with the agreement slot. Sumbatova lists *aq-* both as 'hang' and among
  the light verbs found only in complex verbs; both entries are kept.
* The Muira Dargwa complex predicates of Kalyakin's study, with the position he assigns
  their roots, are in `Studies/Kalyakin2026.lean`.

## References

* [N. Sumbatova, *Dargwa* (2021)][sumbatova-2021]
-/

@[expose] public section

namespace Dargwa

open Morphology

/-! ### Light verbs -/

/-- A light verb is the verbal component of a complex verb. -/
structure LightVerb where
  /-- The stem, without the gender prefix. -/
  stem : String
  /-- Whether the root begins with the gender agreement slot. -/
  agrees : Bool
  /-- The meaning of the homophonous simplex verb, `none` for a light verb found only in
  complex verbs. -/
  heavy : Option String
  deriving DecidableEq, Repr

/-- *b-arq'-* 'do, make', the most common light verb. -/
def make : LightVerb := ⟨"arq'", true, some "do, make"⟩

/-- *b-iχ-* 'become'. -/
def become : LightVerb := ⟨"iχ", true, some "become"⟩

/-- *w-ik'-* 'speak'. -/
def speak : LightVerb := ⟨"ik'", true, some "speak"⟩

/-- *b-at-* 'leave'. -/
def leave : LightVerb := ⟨"at", true, some "leave"⟩

/-- *b-ič-* 'fall'. -/
def fall : LightVerb := ⟨"ič", true, some "fall"⟩

/-- *b-aˁq-* 'hit'. -/
def hit : LightVerb := ⟨"aˁq", true, some "hit"⟩

/-- *b-icː-* 'stand up'. -/
def standUp : LightVerb := ⟨"icː", true, some "stand up"⟩

/-- *b-ig-* 'sit down'. -/
def sitDown : LightVerb := ⟨"ig", true, some "sit down"⟩

/-- *aq-* 'hang'. -/
def hang : LightVerb := ⟨"aq", false, some "hang"⟩

/-- *aʁ-* 'reach'. -/
def reach : LightVerb := ⟨"aʁ", false, some "reach"⟩

/-- *b-ač'-* 'come'. -/
def come : LightVerb := ⟨"ač'", true, some "come"⟩

/-- *le-b-q'-* 'come (here)'. -/
def comeHere : LightVerb := ⟨"le-q'", true, some "come (here)"⟩

/-- *b-arʁ-* 'collect'. -/
def collect : LightVerb := ⟨"arʁ", true, some "collect"⟩

/-- *b-ixː-* 'put'. -/
def put : LightVerb := ⟨"ixː", true, some "put"⟩

/-- *it-* 'beat'. -/
def beat : LightVerb := ⟨"it", false, some "beat"⟩

/-- *ag-* 'go away'. -/
def goAway : LightVerb := ⟨"ag", false, some "go away"⟩

/-- *ʔ-* 'say'. -/
def say : LightVerb := ⟨"ʔ", false, some "say"⟩

/-- *b-erk'-* 'drive'. -/
def drive : LightVerb := ⟨"erk'", true, some "drive"⟩

/-- *arg-* 'sift'. -/
def sift : LightVerb := ⟨"arg", false, some "sift"⟩

/-- *b-ertː-* 'tear'. -/
def tear : LightVerb := ⟨"ertː", true, some "tear"⟩

/-- *b-aˁʜ-* 'struggle'. -/
def struggle : LightVerb := ⟨"aˁʜ", true, some "struggle"⟩

/-- *b-ut'-* 'cut', the light verb of *č'u-b-ut'-* 'divide by two'. -/
def cut : LightVerb := ⟨"ut'", true, some "cut"⟩

/-- *b-uq-*, found only in complex verbs. -/
def uq : LightVerb := ⟨"uq", true, none⟩

/-- *aq-*, found only in complex verbs. -/
def aq : LightVerb := ⟨"aq", false, none⟩

/-- *b-ikː-*, found only in complex verbs. -/
def ikk : LightVerb := ⟨"ikː", true, none⟩

/-- *art-*, found only in complex verbs. -/
def art : LightVerb := ⟨"art", false, none⟩

/-- The light verbs Sumbatova lists. -/
def lightVerbs : Finset LightVerb :=
  {make, become, speak, leave, fall, hit, standUp, sitDown, hang, reach, come, comeHere,
    collect, put, beat, goAway, say, drive, sift, tear, struggle, cut, uq, aq, ikk, art}

/-! ### Complex verbs -/

/-- The word class of the lexical stem of a complex verb as an independent word. -/
inductive StemClass where
  | noun
  | adjective
  | numeral
  | verb
  | ideophone
  deriving DecidableEq, Repr, Fintype

/-- A complex verb is a lexical stem, cited as the root it contributes, followed by a light
verb, with any preverbs between them. -/
structure ComplexVerb where
  /-- The lexical stem, which carries the core meaning of the complex. -/
  stem : Morph
  /-- The word class of the stem, `none` for a stem restricted to the complex verb. -/
  category : Option StemClass
  /-- The preverbs between the stem and the light verb. -/
  preverbs : List Morph := []
  /-- The light verb. -/
  lightVerb : LightVerb
  /-- The meaning of the complex verb. -/
  gloss : String
  deriving DecidableEq, Repr

/-- *taman-b-arq'-* 'finish' (transitive), from *taman* 'end'. -/
def finish : ComplexVerb :=
  { stem := .root "taman", category := some .noun, lightVerb := make, gloss := "finish" }

/-- *ʜaˁdur-d-arq'-* 'prepare', from *ʜaˁdur-* 'ready'. -/
def prepare : ComplexVerb :=
  { stem := .root "ʜaˁdur", category := some .adjective, lightVerb := make,
    gloss := "prepare" }

/-- *č'u-b-ut'-* 'divide by two', from *č'u* 'two'. -/
def divideByTwo : ComplexVerb :=
  { stem := .root "č'u", category := some .numeral, lightVerb := cut,
    gloss := "divide by two" }

/-- *qeʜ-w-ik'-* 'cough' (imperfective), from the ideophone *qeʜ-*. -/
def cough : ComplexVerb :=
  { stem := .root "qeʜ", category := some .ideophone, lightVerb := speak,
    gloss := "cough" }

/-- *w-isːe-w-ig-* 'start crying', from *w-isː-* 'cry' (imperfective). -/
def startCrying : ComplexVerb :=
  { stem := .root "isːe", category := some .verb, lightVerb := sitDown,
    gloss := "start crying" }

/-- *tːurχ-b-arq'-* 'spin', from a stem found nowhere else. -/
def spin : ComplexVerb :=
  { stem := .root "tːurχ", category := none, lightVerb := make, gloss := "spin" }

/-- *t'aš-ka-b-icː-* 'stop', from a stem found nowhere else, with the preverb *ka-*
'downward' between it and the light verb. -/
def stop : ComplexVerb :=
  { stem := .root "t'aš", category := none, preverbs := [.pref "ka"],
    lightVerb := standUp, gloss := "stop" }

end Dargwa
