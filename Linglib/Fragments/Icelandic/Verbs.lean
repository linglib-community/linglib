module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Verb.CaseArray
public import Linglib.Fragments.Icelandic.Case

/-!
# Icelandic verbs

The Icelandic verb as a lexical entry: the root `Verb` with its case array, the case of its
subject followed by the cases of its objects in their unmarked linear order. Icelandic marks
its subjects and objects in every one of its four cases. Of the sixteen case pairs a dyadic
verb might show, [thrainsson-2007]'s overview (4.48) finds five reasonably common,
nominative–accusative, nominative–dative, nominative–genitive, dative–nominative and
accusative–accusative, four rare or special, and seven unattested; of the sixty-four triples,
its table (4.62) finds six, the subject always nominative, from the more than two hundred
nominative–dative–accusative verbs down to the two nominative–accusative–accusative ones.
Verbs in *-st*, whether or not an active counterpart exists (*opna* ~ *opnast*, *leiðast*),
are entries like any other.

## Main definitions

* `Verb`: the entry, the root `Verb` with its `Verb.CaseArray`.
* `verbs`: the entries.

## Main results

* `subject_cases`, `object_cases`: each of the four cases of `Icelandic.Case` is the
  case of some subject and of some object.
* `subject_eq_nom_of_ditransitive`: a verb with two objects has a nominative subject.

## Implementation notes

The entries record the case array and nothing of its provenance: which cases a verb assigns
lexically and which fall out of the configuration is what the accounts of Icelandic case
disagree about, and each study states its own (`Studies/ZaenenMalingThrainsson1985.lean`).
The order of two objects is the one the sources gloss.

## References

* [thrainsson-2007]
* [zaenen-maling-thrainsson-1985]
* [wood-2015]
* [wood-2023]
-/

@[expose] public section

namespace Icelandic.Verbs

/-- An Icelandic verb is the root entry with its case array, the case of its subject and the
cases of its objects in linear order. -/
structure Verb extends _root_.Verb, _root_.Verb.CaseArray Case
  deriving BEq

namespace Verb

/-- The entry for a citation form and its case array. -/
def ofCases (form : String) (subject : Case) (objects : List Case := []) : Verb :=
  { morphs := [.root form], subject, objects }

end Verb

/-! ### Intransitives -/

/-- *dansa* 'dance' ([zaenen-maling-thrainsson-1985] (9), (58)). -/
def dansa : Verb := .ofCases "dansa" .nom

/-- *opnast* 'open', the *-st* form of *opna* ([wood-2015] ch. 3 (52)). -/
def opnast : Verb := .ofCases "opnast" .nom

/-- *splundrast* 'shatter', the *-st* form of *splundra* ([wood-2015] ch. 3 (70)). -/
def splundrast : Verb := .ofCases "splundrast" .nom

/-- *seljast* 'sell', the *-st* form of *selja* ([wood-2015] ch. 2 (1d)). -/
def seljast : Verb := .ofCases "seljast" .nom

/-- *kyssast* 'kiss (each other)', the *-st* form of *kyssa* ([wood-2015] ch. 2 (1a)). -/
def kyssast : Verb := .ofCases "kyssast" .nom

/-- *dulbúast* 'disguise oneself', the *-st* form of *dulbúa* ([wood-2015] ch. 2 (1b)). -/
def dulbuast : Verb := .ofCases "dulbúast" .nom

/-- *reka* 'drift', accusative subject ([thrainsson-2007] (4.30a)). -/
def reka : Verb := .ofCases "reka" .acc

/-- *líða* 'feel', dative subject ([thrainsson-2007] (4.31c)). -/
def lida : Verb := .ofCases "líða" .dat

/-- *gæta* 'be noticeable', genitive subject ([thrainsson-2007] (4.32a)). -/
def gaeta : Verb := .ofCases "gæta" .gen

/-! ### Nominative subjects -/

/-- *elska* 'love', nominative–accusative ([wood-2015] ch. 3 (11a)). -/
def elska : Verb := .ofCases "elska" .nom [.acc]

/-- *lesa* 'read', nominative–accusative ([thrainsson-2007] (4.56b)). -/
def lesa : Verb := .ofCases "lesa" .nom [.acc]

/-- *kyssa* 'kiss', nominative–accusative ([zaenen-maling-thrainsson-1985] (22a)). -/
def kyssa : Verb := .ofCases "kyssa" .nom [.acc]

/-- *opna* 'open', nominative–accusative ([wood-2023] (2.93a)). -/
def opna : Verb := .ofCases "opna" .nom [.acc]

/-- *hjálpa* 'help', nominative–dative ([zaenen-maling-thrainsson-1985] (8a)). -/
def hjalpa : Verb := .ofCases "hjálpa" .nom [.dat]

/-- *strjúka* 'pet, stroke', nominative–dative ([thrainsson-2007] (4.57b)). -/
def strjuka : Verb := .ofCases "strjúka" .nom [.dat]

/-- *kasta* 'throw', nominative–dative ([thrainsson-2007] (4.57c); [wood-2015] ch. 5
(48a)). -/
def kasta : Verb := .ofCases "kasta" .nom [.dat]

/-- *splundra* 'shatter', nominative–dative ([wood-2015] ch. 5 (53a)). -/
def splundra : Verb := .ofCases "splundra" .nom [.dat]

/-- *klæðast* 'dress in', the *-st* form of *klæða*, nominative–dative
([wood-2015] ch. 6 (76b)). -/
def klaedast : Verb := .ofCases "klæðast" .nom [.dat]

/-- *sakna* 'miss', nominative–genitive ([zaenen-maling-thrainsson-1985] (8b), (14a)). -/
def sakna : Verb := .ofCases "sakna" .nom [.gen]

/-- *krefjast* 'demand', the *-st* form of *krefja*, nominative–genitive ([thrainsson-2007]
(4.58b)). -/
def krefjast : Verb := .ofCases "krefjast" .nom [.gen]

/-- *óska* 'wish', nominative–genitive, or nominative–dative–genitive with the recipient
([zaenen-maling-thrainsson-1985] (37e), (66); [thrainsson-2007] (4.69a)). -/
def oska : Verb := .ofCases "óska" .nom [.dat, .gen]

/-! ### Oblique subjects -/

/-- *þykja* 'find, seem', dative–nominative ([zaenen-maling-thrainsson-1985] (13)). -/
def thykja : Verb := .ofCases "þykja" .dat [.nom]

/-- *finnast* 'find, think', dative–nominative ([zaenen-maling-thrainsson-1985] (27a)). -/
def finnast : Verb := .ofCases "finnast" .dat [.nom]

/-- *líka* 'like', dative–nominative ([thrainsson-2007] (4.61b); [wood-2015] ch. 5 (94a)). -/
def lika : Verb := .ofCases "líka" .dat [.nom]

/-- *batna* 'recover from', dative–nominative ([thrainsson-2007] (4.61c)). -/
def batna : Verb := .ofCases "batna" .dat [.nom]

/-- *leiðast* 'be bored by', dative–nominative ([wood-2015] ch. 5 (92a)). -/
def leidast : Verb := .ofCases "leiðast" .dat [.nom]

/-- *áskotnast* 'come by', dative–nominative ([wood-2015] ch. 5 (41a)). -/
def askotnast : Verb := .ofCases "áskotnast" .dat [.nom]

/-- *vanta* 'lack, need', accusative–accusative ([zaenen-maling-thrainsson-1985] (29a)). -/
def vanta : Verb := .ofCases "vanta" .acc [.acc]

/-- *dreyma* 'dream', accusative–accusative ([thrainsson-2007] (4.60b)). -/
def dreyma : Verb := .ofCases "dreyma" .acc [.acc]

/-- *bresta* 'lack', accusative–accusative ([thrainsson-2007] (4.60c); [wood-2015] ch. 2
(77a)). -/
def bresta : Verb := .ofCases "bresta" .acc [.acc]

/-- *sækja* 'come over', accusative–nominative, one of the rare accusative–nominative verbs
([thrainsson-2007] (4.52a)). -/
def saekja : Verb := .ofCases "sækja" .acc [.nom]

/-- *iðra* 'regret', accusative–genitive, one of the rare accusative–genitive verbs
([thrainsson-2007] (4.52b)). -/
def idra : Verb := .ofCases "iðra" .acc [.gen]

/-! ### Ditransitives -/

/-- *gefa* 'give', nominative–dative–accusative ([zaenen-maling-thrainsson-1985] (44),
(65a)). -/
def gefa : Verb := .ofCases "gefa" .nom [.dat, .acc]

/-- *segja* 'tell', nominative–dative–accusative ([zaenen-maling-thrainsson-1985] (37c)). -/
def segja : Verb := .ofCases "segja" .nom [.dat, .acc]

/-- *sýna* 'show', nominative–dative–accusative ([thrainsson-2007] (4.63b)). -/
def syna : Verb := .ofCases "sýna" .nom [.dat, .acc]

/-- *senda* 'send', nominative–dative–accusative ([thrainsson-2007] (4.63c)). -/
def senda : Verb := .ofCases "senda" .nom [.dat, .acc]

/-- *leyna* 'conceal from', nominative–accusative–dative ([zaenen-maling-thrainsson-1985]
(37a)). -/
def leyna : Verb := .ofCases "leyna" .nom [.acc, .dat]

/-- *svipta* 'deprive of', nominative–accusative–dative ([zaenen-maling-thrainsson-1985]
(64a)). -/
def svipta : Verb := .ofCases "svipta" .nom [.acc, .dat]

/-- *ræna* 'rob of', nominative–accusative–dative ([thrainsson-2007] (4.65c)). -/
def raena : Verb := .ofCases "ræna" .nom [.acc, .dat]

/-- *biðja* 'ask for', nominative–accusative–genitive ([zaenen-maling-thrainsson-1985]
(37b); [thrainsson-2007] (4.70c)). -/
def bidja : Verb := .ofCases "biðja" .nom [.acc, .gen]

/-- *krefja* 'demand of', nominative–accusative–genitive ([thrainsson-2007] (4.70b)). -/
def krefja : Verb := .ofCases "krefja" .nom [.acc, .gen]

/-- *spyrja* 'ask', nominative–accusative–genitive ([wood-2015] ch. 2 (81a)). -/
def spyrja : Verb := .ofCases "spyrja" .nom [.acc, .gen]

/-- *lofa* 'promise', nominative–dative–dative ([zaenen-maling-thrainsson-1985] (37d)). -/
def lofa : Verb := .ofCases "lofa" .nom [.dat, .dat]

/-- *skila* 'return', nominative–dative–dative ([zaenen-maling-thrainsson-1985] (42a);
[thrainsson-2007] (4.72b)). -/
def skila : Verb := .ofCases "skila" .nom [.dat, .dat]

/-- *valda* 'cause', nominative–dative–dative ([thrainsson-2007] (4.72c)). -/
def valda : Verb := .ofCases "valda" .nom [.dat, .dat]

/-- *synja* 'deny', nominative–dative–genitive ([thrainsson-2007] (4.69b)). -/
def synja : Verb := .ofCases "synja" .nom [.dat, .gen]

/-- *kosta* 'cost', nominative–accusative–accusative, one of the two such verbs
([thrainsson-2007] (4.74a)). -/
def kosta : Verb := .ofCases "kosta" .nom [.acc, .acc]

/-- *taka* 'take (time)', nominative–accusative–accusative ([thrainsson-2007] (4.74b)). -/
def taka : Verb := .ofCases "taka" .nom [.acc, .acc]

/-- The verbs of the fragment. -/
def verbs : List Verb :=
  [dansa, opnast, splundrast, seljast, kyssast, dulbuast, reka, lida, gaeta, elska, lesa, kyssa,
    opna, hjalpa, strjuka, kasta, splundra, klaedast, sakna, krefjast, oska, thykja, finnast, lika,
    batna, leidast, askotnast, vanta, dreyma, bresta, saekja, idra, gefa, segja, syna, senda,
    leyna, svipta, raena, bidja, krefja, spyrja, lofa, skila, valda, synja, kosta, taka]

/-! ### The cases on the verb

Every one of the four cases marks subjects and objects. [thrainsson-2007]'s (4.30) to (4.32)
set accusative, dative and genitive subjects beside the nominative ones, and its (4.61) the
nominative objects of the dative-subject verbs beside the accusative, dative and genitive
objects of (4.56) to (4.58). The triadic verbs of its table (4.62) all have nominative
subjects. -/

/-- Each of the four cases is the case of some subject. -/
theorem subject_cases : (verbs.map (·.subject)).toFinset = Finset.univ := by decide

/-- Each of the four cases is the case of some object. -/
theorem object_cases : (verbs.flatMap (·.objects)).toFinset = Finset.univ := by decide

/-- A verb with two objects has a nominative subject. -/
theorem subject_eq_nom_of_ditransitive :
    ∀ v ∈ verbs, v.objects.length = 2 → v.subject = .nom := by
  decide

end Icelandic.Verbs
