module

public import Linglib.Phonology.Segmental.Defs
public import Linglib.Fragments.Mayan.Agreement
public import Linglib.Syntax.Clause.ArgumentRole

/-!
# Chol agreement

Chol cross-references the core arguments with two sets of person markers: Set A, the prefixes
*k-*, *a-* and *i-*, before a vowel *k-*, *aw-* and *(i)y-*, which index transitive subjects and
possessors, and Set B, the suffixes *-oñ*, *-ety* and zero, which index transitive objects.
Plurality is carried by clitics common to both sets, *=la* for the inclusive first and for the
second person and *=l(oj)oñ* for the exclusive first, and by the suffix *-ob* for the third.
The aspect markers are auxiliaries, the perfective *tyi* and the imperfective *mi*, and the
verbal complex after them runs Set A, stem, status suffix, Set B, so that Set B follows the stem
and Chol is a low-absolutive language. The alignment splits by aspect: in the perfective the
intransitive subject takes Set B, the ergative pattern, and in every other aspect it takes Set
A, the pattern Vázquez Álvarez calls nominative–accusative and Coon, reading the non-perfective
clause as a nominalization under an aspectual predicate, extended ergative. Within the
perfective the intransitives divide further: agentive verbs such as *k'ay* 'sing' index their
subject with Set A on the light verb *cha'l*, non-agentive verbs such as *majl* 'go' with Set B
on the verb, and a third class such as *wäy* 'sleep' allows both. Vázquez Álvarez's grammar and
Coon's sketch are the sources.

## Main definitions

* `Chol.setAExponent`, `Chol.setBExponent`: the two paradigms, the plural cells with the
  inclusive clitic.
* `Chol.template`, `Chol.markerSet`: the verbal complex and the marking of the arguments by
  aspect.
* `Chol.IntransitiveClass`, `Chol.Intransitive`, `Chol.intransitives`: the three classes of
  intransitive verb by the marking of their subject in the perfective, with the grammar's
  examples.

## Implementation notes

The plural cells carry the inclusive *=la*, the exclusive *=l(oj)oñ* having no cell in the
person–number bundles. The first person prefix is *j-* before a stem-initial *k*.

## References

* [vazquez-alvarez-2011]
* [coon-2017]
* [coon-2013]
* [imanishi-2020]
* [coon-mateo-pedro-preminger-2014]
-/

@[expose] public section

namespace Chol

open Mayan (ExponentTable MarkerSet)

/-! ### The verbal complex -/

/-- The position classes of the verbal complex, the aspect marker and Set A before the stem and
the status suffix and then Set B after it. -/
def template : Morphology.AffixTemplate Mayan.VerbSlot :=
  { prefixSlots := [.aspect, .setA], suffixSlots := [.status, .setB] }

/-- Chol is ergative in the perfective and puts Set A on every subject in the other aspects,
the extended ergative pattern. -/
def markerSet : UD.Aspect → ArgumentRole → Option MarkerSet
  | .Perf => Mayan.ergativeMarking
  | .Imp | .Prog | .Prosp | .Hab | .Iter => Mayan.extendedErgativeMarking

/-! ### The paradigms -/

/-- The Set A markers by the following segment, with the plural clitic *=la* and the third
person plural suffix *-ob*. -/
def setAExponent : Phonology.Segment.Class → ExponentTable
  | .consonant =>
    [(.personNumber .first .singular, [.pref "k"]), (.personNumber .second .singular, [.pref "a"]),
     (.personNumber .third .singular, [.pref "i"]),
     (.personNumber .first .plural, [.pref "k", .encl "la"]),
     (.personNumber .second .plural, [.pref "a", .encl "la"]),
     (.personNumber .third .plural, [.pref "i", .suff "ob"])]
  | .vowel =>
    [(.personNumber .first .singular, [.pref "k"]), (.personNumber .second .singular, [.pref "aw"]),
     (.personNumber .third .singular, [.pref "iy"]),
     (.personNumber .first .plural, [.pref "k", .encl "la"]),
     (.personNumber .second .plural, [.pref "aw", .encl "la"]),
     (.personNumber .third .plural, [.pref "iy", .suff "ob"])]

/-- The Set B markers, with a zero third person singular, the plural clitic *=la* and the third
person plural *-ob*. -/
def setBExponent : ExponentTable :=
  [(.personNumber .first .singular, [.suff "oñ"]), (.personNumber .second .singular, [.suff "ety"]),
   (.personNumber .third .singular, []),
   (.personNumber .first .plural, [.suff "oñ", .encl "la"]),
   (.personNumber .second .plural, [.suff "ety", .encl "la"]),
   (.personNumber .third .plural, [.suff "ob"])]

/-! ### Intransitive classes -/

/-- The three classes of intransitive verb by the marking of their subject in the perfective:
Set A on the light verb *cha'l*, Set B on the verb, or either. -/
inductive IntransitiveClass where
  | agentive
  | nonAgentive
  | fluid
  deriving DecidableEq, Repr, Fintype

/-- An intransitive verb with its class. -/
structure Intransitive where
  /-- The root. -/
  form : String
  /-- The gloss. -/
  gloss : String
  /-- The class by the marking of the subject. -/
  marking : IntransitiveClass
  deriving DecidableEq, Repr

/-- *ajñel* 'run', agentive. -/
def ajñel : Intransitive := ⟨"ajñel", "run", .agentive⟩

/-- *oñel* 'shout', agentive. -/
def oñel : Intransitive := ⟨"oñel", "shout", .agentive⟩

/-- *tse'ñal* 'laugh', agentive. -/
def tse'ñal : Intransitive := ⟨"tse'ñal", "laugh", .agentive⟩

/-- *k'ay* 'sing', agentive. -/
def k'ay : Intransitive := ⟨"k'ay", "sing", .agentive⟩

/-- *majl* 'go', non-agentive. -/
def majl : Intransitive := ⟨"majl", "go", .nonAgentive⟩

/-- *lets* 'climb', non-agentive. -/
def lets : Intransitive := ⟨"lets", "climb", .nonAgentive⟩

/-- *chäm* 'die', non-agentive. -/
def chäm : Intransitive := ⟨"chäm", "die", .nonAgentive⟩

/-- *tyojm* 'explode', non-agentive. -/
def tyojm : Intransitive := ⟨"tyojm", "explode", .nonAgentive⟩

/-- *jil* 'finish', non-agentive. -/
def jil : Intransitive := ⟨"jil", "finish", .nonAgentive⟩

/-- *wäy* 'sleep', of either marking. -/
def wäy : Intransitive := ⟨"wäy", "sleep", .fluid⟩

/-- *uk'* 'cry', of either marking. -/
def uk' : Intransitive := ⟨"uk'", "cry", .fluid⟩

/-- *ts'äm* 'bathe', of either marking. -/
def ts'äm : Intransitive := ⟨"ts'äm", "bathe", .fluid⟩

/-- *tyijp'* 'jump', of either marking. -/
def tyijp' : Intransitive := ⟨"tyijp'", "jump", .fluid⟩

/-- The intransitives of the grammar's alignment examples. -/
def intransitives : List Intransitive :=
  [ajñel, oñel, tse'ñal, k'ay, majl, lets, chäm, tyojm, jil, wäy, uk', ts'äm, tyijp']

end Chol
