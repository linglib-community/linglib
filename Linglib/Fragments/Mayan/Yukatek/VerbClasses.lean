module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Aspect.Defs

/-!
# Yukatek Maya verb classes and status

A Yukatek Maya verb is inflected for status, a suffixal category of aspect and mood with
four values, the incompletive, the completive, the subjunctive, which Hofling calls the
dependent, and the imperative. The allomorphs of the status suffixes sort verb stems into five
classes: the active intransitives, unmarked in the incompletive, the inactive intransitives,
unmarked in the completive, the inchoatives derived from stative roots, the positionals of
spatial configurations, and the transitives. The status also fixes which set of person
markers cross-references the sole argument of an intransitive, the split that
`Yukatek.markerSet` records. Bohnemeyer's tables of status semantics and status
patterns and Hofling's Yucatecan sketch are the sources; the verbs are those of Bohnemeyer's
examples, whose classification by causation and linking is the matter of
`Studies/Bohnemeyer2004.lean`.

## Main definitions

* `Yukatek.StatusCategory`, `Yukatek.VerbStemClass`, `Yukatek.statusSuffix`: the four statuses,
  the five stem classes, and the status suffix of each class.
* `Yukatek.Verb`, `Yukatek.verbs`: the verbs of Bohnemeyer's examples with their stem classes.

## Implementation notes

The suffixes are written as Bohnemeyer prints them, *V* for the harmonic vowel and a slash
between allomorphs; the imperfective reading of the incompletive and the perfective reading of
the completive and the subjunctive are his glosses of the statuses.

## References

* [bohnemeyer-2004]
* [hofling-2017]
-/

@[expose] public section

namespace Yukatek

open Aspect (Perfectivity)

/-! ### Status -/

/-- The four status categories. -/
inductive StatusCategory where
  | incompletive
  | completive
  | subjunctive
  | imperative
  deriving DecidableEq, Repr, Fintype

/-- The viewpoint aspect a status expresses, imperfective in the incompletive and perfective in
the completive and the subjunctive; the imperative expresses none. -/
def StatusCategory.viewpointAspect : StatusCategory → Option Perfectivity
  | .incompletive => some .imperfective
  | .completive | .subjunctive => some .perfective
  | .imperative => none

/-! ### Stem classes -/

/-- The five verb stem classes, distinguished by their status allomorphs. -/
inductive VerbStemClass where
  | active
  | inactive
  | inchoative
  | positional
  | transitiveActive
  deriving DecidableEq, Repr, Fintype

/-- The status suffix of each stem class, `none` where the class has no form in the status. -/
def statusSuffix : VerbStemClass → StatusCategory → Option String
  | .active, .incompletive => some "-ø"
  | .active, .completive => some "-nah"
  | .active, .subjunctive => some "-nak"
  | .active, .imperative => some "-nen"
  | .inactive, .incompletive => some "-Vl"
  | .inactive, .completive => some "-ø"
  | .inactive, .subjunctive => some "-Vk"
  | .inactive, .imperative => some "-en"
  | .inchoative, .incompletive => some "-tal"
  | .inchoative, .completive => some "-chah"
  | .inchoative, .subjunctive => some "-chahak"
  | .inchoative, .imperative => none
  | .positional, .incompletive => some "-tal"
  | .positional, .completive => some "-lah"
  | .positional, .subjunctive => some "-l(ah)ak"
  | .positional, .imperative => some "-len"
  | .transitiveActive, .incompletive => some "-ik"
  | .transitiveActive, .completive => some "-ah"
  | .transitiveActive, .subjunctive => some "-ø/-eh"
  | .transitiveActive, .imperative => some "-ø/-eh"

/-! ### Verbs -/

/-- A verb with its stem class. -/
structure Verb where
  /-- The stem, in Bohnemeyer's orthography. -/
  form : String
  /-- The gloss. -/
  gloss : String
  /-- The stem class. -/
  stemClass : VerbStemClass
  deriving DecidableEq, Repr

/-- *meyah* 'work', active. -/
def meyah : Verb := ⟨"meyah", "work", .active⟩

/-- *bàaxal* 'play', active. -/
def bàaxal : Verb := ⟨"bàaxal", "play", .active⟩

/-- *balak'* 'roll', active. -/
def balak' : Verb := ⟨"balak'", "roll", .active⟩

/-- *péek* 'move, wiggle', active. -/
def péek : Verb := ⟨"péek", "move", .active⟩

/-- *tsíirin* 'buzz', active. -/
def tsíirin : Verb := ⟨"tsíirin", "buzz", .active⟩

/-- *chíik* 'shake, rattle', active. -/
def chíik : Verb := ⟨"chíik", "shake", .active⟩

/-- *háarax* 'slide', active. -/
def háarax : Verb := ⟨"háarax", "slide", .active⟩

/-- *húuy* 'stir, agitate', active. -/
def húuy : Verb := ⟨"húuy", "stir", .active⟩

/-- *mosòon* 'whirl, revolve', active. -/
def mosòon : Verb := ⟨"mosòon", "whirl", .active⟩

/-- *pirix* 'flick', active. -/
def pirix : Verb := ⟨"pirix", "flick", .active⟩

/-- *walak'* 'turn, revolve', active. -/
def walak' : Verb := ⟨"walak'", "turn", .active⟩

/-- *nik'ich* 'squeak', active. -/
def nik'ich : Verb := ⟨"nik'ich", "squeak", .active⟩

/-- *kim* 'die', inactive. -/
def kim : Verb := ⟨"kim", "die", .inactive⟩

/-- *lúub* 'fall', inactive. -/
def lúub : Verb := ⟨"lúub", "fall", .inactive⟩

/-- *hàan* 'eat', inactive. -/
def hàan : Verb := ⟨"hàan", "eat", .inactive⟩

/-- *ka'n* 'get tired', inactive. -/
def ka'n : Verb := ⟨"ka'n", "get tired", .inactive⟩

/-- *na'k* 'ascend', inactive. -/
def na'k : Verb := ⟨"na'k", "ascend", .inactive⟩

/-- *la'b* 'deteriorate', inactive. -/
def la'b : Verb := ⟨"la'b", "deteriorate", .inactive⟩

/-- *t'íil* 'last, drag on', inactive. -/
def t'íil : Verb := ⟨"t'íil", "last", .inactive⟩

/-- *ts'u'k* 'rot', inactive. -/
def ts'u'k : Verb := ⟨"ts'u'k", "rot", .inactive⟩

/-- *bòox-tal* 'blacken', inchoative. -/
def bòoxtal : Verb := ⟨"bòox-tal", "blacken", .inchoative⟩

/-- *chichan-tal* 'shrink', inchoative. -/
def chichantal : Verb := ⟨"chichan-tal", "shrink", .inchoative⟩

/-- *kul-tal* 'sit down', positional. -/
def kultal : Verb := ⟨"kul-tal", "sit down", .positional⟩

/-- *wa'l-tal* 'stand up', positional. -/
def wa'ltal : Verb := ⟨"wa'l-tal", "stand up", .positional⟩

/-- *chil-tal* 'lie down', positional. -/
def chiltal : Verb := ⟨"chil-tal", "lie down", .positional⟩

/-- *xol-tal* 'kneel', positional. -/
def xoltal : Verb := ⟨"xol-tal", "kneel", .positional⟩

/-- *hats'* 'hit', transitive. -/
def hats' : Verb := ⟨"hats'", "hit", .transitiveActive⟩

/-- The verbs of Bohnemeyer's examples. -/
def verbs : List Verb :=
  [meyah, bàaxal, balak', péek, tsíirin, chíik, háarax, húuy, mosòon, pirix, walak', nik'ich,
    kim, lúub, hàan, ka'n, na'k, la'b, t'íil, ts'u'k, bòoxtal, chichantal, kultal, wa'ltal,
    chiltal, xoltal, hats']

end Yukatek
