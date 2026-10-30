module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Category.Complementizer.Basic

/-!
# Bulgarian clausal embedding

Bulgarian (Slavic, ISO 639-3 `bul`) introduces a finite complement clause with the default
complementizer *če* 'that'. With a class of emotive factive predicates such as *săžaljavam*
'regret', *radvam se* 'be happy' and *sram me e* 'feel ashamed', the invariant relativizer
*deto* introduces the complement as well, alternating freely with *če* apart from register, and
also in the form *zadeto*. These predicates all take a *za* 'for' prepositional phrase beside
the clause. The transitive factives *razbiram* 'comprehend', *vzemam predvid* 'take into
account', *imam predvid* 'bear in mind', *prenebregvam* 'ignore' and *griža se* 'take care',
the emotive *văzmuštavam se* 'resent', which takes no *za* phrase, and the semi-factives
*znaja* 'know', *pomnja* 'remember', *otkrivam* 'find out', *viždam* 'see', *čuvam* 'hear' and
*zabeljazvam* 'notice' take *če* only.

Forms follow Krapova's scientific transliteration, *ă* for ъ; several citation forms are
multiword impersonals with an experiencer clitic, as *jad me e*. The predicate lists are the
ones Krapova names and are open-ended in the paper. The data are Krapova's; the hidden-relative
analysis of *deto* and the double requirement behind its distribution are stated in
`Studies/Deal2026.lean`.

## Implementation notes

*deto* and *zadeto* record the coding and sentence type of *če*, so `Verb.Takes`, which selects
by those, takes all three alike. The predicates *deto* introduces are `detoTakers`, a lexical
list, which `Studies/Deal2026.lean` proves the double requirement picks out.

## References

* [krapova-2010]
* [kiparsky-kiparsky-1970]
* [karttunen-1971b]
-/

@[expose] public section

namespace Bulgarian

/-! ### Clause-typers -/

/-- The default complementizer *če* 'that', available in every complement clause (fn. 46). -/
def che : Complementizer where
  morphs := [.free "če"]
  coding := some .indicative
  types := .only .declarative

/-- The invariant relativizer *deto*, which also introduces the complements of the emotive
factives that take a *za* phrase, alternating with *če* (§5). -/
def deto : Complementizer where
  morphs := [.free "deto"]
  coding := some .indicative
  types := .only .declarative

/-- The form *zadeto* of the same complementizer (fn. 45). -/
def zadeto : Complementizer := { deto with morphs := [.free "zadeto"] }

/-! ### Predicates -/

/-- The valency of an emotive factive, a finite clause or a *za* phrase (59). -/
def emotiveValency : Verb.Valency :=
  .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.pp]

/-- *săžaljavam* 'regret', the predicate of the projection trials (57). -/
def sazhaljavam : Verb where
  morphs := [.root "săžaljavam"]
  valency := emotiveValency
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *vinoven săm* 'be one's fault' ((57b)). -/
def vinovenSam : Verb where
  morphs := [.root "vinoven", .free "săm"]
  valency := emotiveValency
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *jad me e* 'be sorry, regret' ((56b)). -/
def jadMeE : Verb where
  morphs := [.root "jad", .free "me", .free "e"]
  valency := emotiveValency
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *radvam se* 'be happy'. -/
def radvamSe : Verb where
  morphs := [.root "radvam", .free "se"]
  valency := emotiveValency
  attitude := some (.preferential .positive true)
  factivity := some .full

/-- *nedovolstvam* 'be dissatisfied'. -/
def nedovolstvam : Verb where
  morphs := [.root "nedovolstvam"]
  valency := emotiveValency
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *pritesnjavam se* 'worry'. -/
def pritesnjavamSe : Verb where
  morphs := [.root "pritesnjavam", .free "se"]
  valency := emotiveValency
  attitude := some (.preferential .negative false)
  factivity := some .full

/-- *žal mi e* 'be sorry'. -/
def zhalMiE : Verb where
  morphs := [.root "žal", .free "mi", .free "e"]
  valency := emotiveValency
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *măčno mi e* 'be sad'. -/
def machnoMiE : Verb where
  morphs := [.root "măčno", .free "mi", .free "e"]
  valency := emotiveValency
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *sram me e* 'feel ashamed'. -/
def sramMeE : Verb where
  morphs := [.root "sram", .free "me", .free "e"]
  valency := emotiveValency
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *văzmuštavam se* 'resent', emotive and factive but without a *za* phrase ((58a)). -/
def vazmushtavamSe : Verb where
  morphs := [.root "văzmuštavam", .free "se"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative true)
  factivity := some .full

/-- *razbiram* 'comprehend', a transitive factive on Kiparsky and Kiparsky's list. -/
def razbiram : Verb where
  morphs := [.root "razbiram"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .full

/-- *vzemam predvid* 'take into account', printed *previd* in the paper. -/
def vzemamPredvid : Verb where
  morphs := [.root "vzemam", .free "predvid"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .full

/-- *imam predvid* 'bear in mind'. -/
def imamPredvid : Verb where
  morphs := [.root "imam", .free "predvid"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .full

/-- *prenebregvam* 'ignore'. -/
def prenebregvam : Verb where
  morphs := [.root "prenebregvam"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .full

/-- *griža se* 'take care'. -/
def grizhaSe : Verb where
  morphs := [.root "griža", .free "se"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .full

/-- *znaja* 'know', a semi-factive. -/
def znaja : Verb where
  morphs := [.root "znaja"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-- *pomnja* 'remember'. -/
def pomnja : Verb where
  morphs := [.root "pomnja"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .semi

/-- *otkrivam* 'find out'. -/
def otkrivam : Verb where
  morphs := [.root "otkrivam"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .semi

/-- *viždam* 'see', on the propositional reading. -/
def vizhdam : Verb where
  morphs := [.root "viždam"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .semi

/-- *čuvam* 'hear', on the propositional reading. -/
def chuvam : Verb where
  morphs := [.root "čuvam"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .semi

/-- *zabeljazvam* 'notice'. -/
def zabeljazvam : Verb where
  morphs := [.root "zabeljazvam"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  factivity := some .semi

/-- The predicates Krapova names. -/
def verbs : List Verb :=
  [sazhaljavam, vinovenSam, jadMeE, radvamSe, nedovolstvam, pritesnjavamSe, zhalMiE, machnoMiE,
    sramMeE, vazmushtavamSe, razbiram, vzemamPredvid, imamPredvid, prenebregvam, grizhaSe,
    znaja, pomnja, otkrivam, vizhdam, chuvam, zabeljazvam]

/-- The predicates whose complement *deto* may introduce (§5). -/
def detoTakers : List Verb :=
  [sazhaljavam, vinovenSam, jadMeE, radvamSe, nedovolstvam, pritesnjavamSe, zhalMiE, machnoMiE,
    sramMeE]

end Bulgarian
