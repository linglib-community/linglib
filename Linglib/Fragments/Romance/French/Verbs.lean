module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# French verbs

This file defines the French verb entries: the causatives *faire* and *laisser*, the attitude
verbs *vouloir*, *espérer* and *croire* with the mood of the clause each selects, the
anticausatives of the causative alternation whose *se* is optional, and the transitive verbs
whose passive agent is marked by *par* or *de*. An entry is a `Verb` with its argument frames
and the proto-role entailments of its arguments in the sense of Dowty. Martin, Schäfer and
Kastner sort the anticausatives by whether a human undergoer typically controls the change,
and Staps and Rooryck group the transitive verbs by the agent preposition they take; both
classifications are the papers' and live in their studies, while the entries here carry the
frames and entailments the classifications are read from. A polysemous verb has one entry per
sense, told apart by its `SenseTag`.

The monadic entries carry the perfect auxiliaries Grevisse and Goosse give them
(`Verb.perfectAuxiliaries`). A closed list of intransitive verbs, "for the most part" of motion or
change of state, forms its perfect with *être*; a longer list takes *avoir* for the action and
*être* for the state that results; every other verb takes *avoir*. The list is the norm and meaning
does not decide it: every verb of the first list is telic or continues a state, but telic verbs
of the second, as *aboutir* 'succeed' and *disparaître* 'disappear', take *avoir* for the action.
A verb of manner of motion selects no directional phrase, so *Marie a couru jusqu'à la maison*
'Marie ran home' keeps *avoir*.

## Main definitions

* `undergoer`, `movingUndergoer`: the entailments of an anticausative's sole argument, without
  and with movement.
* `independentParticipant`, `companionSubject`, `neglectSubject`: the entailments of the
  arguments the transitive entries do not share with a template.
* `allVerbs`: the entries.

## Implementation notes

The basic diathesis of an anticausative is intransitive, its patient the subject, carrying the
entry's profile; the second diathesis is the transitive one, with the patient as object and a
causer as subject. The entries record no
inflectional forms.

## References

* [dowty-1991]
* [martin-schaefer-kastner-2025]
* [staps-rooryck-2024]
* [authier-revuz-1972]
* [grevisse-goosse-2008]
* [sorace-2000]
* [portner-rubinstein-2020]
-/

@[expose] public section

namespace French.Verbs

open ArgumentStructure

/-! ### Causatives -/

/-- *faire* 'make', the causative that forms one predicate with its infinitive, as in *faire
lire* 'make read'. -/
def faire : Verb where
  morphs := [.root "faire"]
  valency := .ofFrame ArgumentFrame.smallClause.withObject (controller := some 1)

/-- *laisser* 'let', the permissive causative. -/
def laisser : Verb where
  morphs := [.root "laisser"]
  valency := .ofFrame ArgumentFrame.smallClause.withObject (controller := some 1)

/-! ### Anticausatives

The anticausatives with an optional *se* that Martin, Schäfer and Kastner test: the verbs of
their experiment 1a, whose change a human undergoer typically does not control, and the verbs
of their experiment 1b, whose change the undergoer typically controls. -/

/-- The sole argument of an anticausative undergoes the change, is causally affected and
exists independently of the event. It is not entailed to be sentient, as *le mur rougit* 'the
wall reddened' shows, nor to be stationary, which is relative to another participant. -/
def undergoer : EntailmentProfile :=
  {.independentExistence, .changeOfState, .causallyAffected}

/-- The sole argument of an anticausative of motion or posture is an `undergoer` that also
moves. -/
def movingUndergoer : EntailmentProfile := insert .movement undergoer

/-- The entry of an anticausative with an optional *se* has the intransitive, its patient the
subject, as its basic diathesis and the transitive of the alternation after it. -/
def anticausative (form : String) (arg : EntailmentProfile := undergoer) : Verb :=
  { morphs := [.root form],
    valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.np, [1, 0])] [some arg,
                    none] }

/-- *brunir* 'turn brown(er)' ([martin-schaefer-kastner-2025] (31)). -/
def brunir : Verb := anticausative "brunir"

/-- *noircir* 'blacken' ([martin-schaefer-kastner-2025] (31)). -/
def noircir : Verb := anticausative "noircir"

/-- *pâlir* 'get pale' ([martin-schaefer-kastner-2025] (31)). -/
def palir : Verb := anticausative "pâlir"

/-- *rajeunir* 'get young(er)' ([martin-schaefer-kastner-2025] (31)). -/
def rajeunir : Verb := { anticausative "rajeunir" with perfectAuxiliaries := {.be, .have} }

/-- *rougir* 'redden, blush' ([martin-schaefer-kastner-2025] (31)). -/
def rougir : Verb := anticausative "rougir"

/-- *approcher (de)* 'get close(r) to', whose undergoer moves
([martin-schaefer-kastner-2025] (40)). -/
def approcher : Verb := anticausative "approcher" movingUndergoer

/-- *durcir* 'harden' ([martin-schaefer-kastner-2025] (40)). -/
def durcir : Verb := anticausative "durcir"

/-- *plier* 'bend', whose undergoer changes posture ([martin-schaefer-kastner-2025] (40)). -/
def plier : Verb := anticausative "plier" movingUndergoer

/-- *radoucir* 'get soft(er)' ([martin-schaefer-kastner-2025] (40)). -/
def radoucir : Verb := anticausative "radoucir"

/-- *refroidir* 'get cold(er)' ([martin-schaefer-kastner-2025] (40)). -/
def refroidir : Verb := anticausative "refroidir"

/-! ### Transitive verbs

The verbs of Staps and Rooryck's Table 1 and of the sections that follow it, with the
proto-role entailments of their subject and object. The prototypically transitive verbs have
the accomplishment template's profiles, the psych verbs an experiencer subject, and the verbs
of following and accompaniment an object that merely exists independently of the event. -/

/-- An argument entailed only to exist independently of the event, neither agentive nor
affected, as the object of a psych verb or of a verb of accompaniment is, and the subject of a
stative positional verb. -/
def independentParticipant : EntailmentProfile := {.independentExistence}

/-- The subject of *accompagner* is sentient and moves but is not entailed to be volitional,
since the accompanying party may merely watch ([staps-rooryck-2024] §3.2). -/
def companionSubject : EntailmentProfile :=
  {.sentience, .movement, .independentExistence}

/-- The subject of the neglect reading of *abandonner* and *délaisser* is volitional and
sentient but brings about no change. -/
def neglectSubject : EntailmentProfile :=
  {.volition, .sentience, .independentExistence}

/-- The entry of a transitive verb with the given subject and object entailments, Vendler
class and sense. -/
def transitive (form : String) (subj obj : EntailmentProfile) (cls : Aspect.VendlerClass)
    (tag : SenseTag := .default) : Verb :=
  { morphs := [.root form], valency := .ofFrame ArgumentFrame.np [some subj, some obj],
    vendlerClass := some cls, senseTag := tag }

/-- *laver* 'wash' ([staps-rooryck-2024] Table 1). -/
def laver : Verb :=
  transitive "laver" accomplishmentSubjectProfile accomplishmentObjectProfile .accomplishment

/-- *briser* 'break' ([staps-rooryck-2024] Table 1). -/
def briser : Verb :=
  transitive "briser" accomplishmentSubjectProfile accomplishmentObjectProfile .achievement

/-- *écrire* 'write', a verb of creation ([staps-rooryck-2024] Table 1). -/
def ecrire : Verb :=
  transitive "écrire" accomplishmentSubjectProfile creationObject .accomplishment

/-- *construire* 'build', a verb of creation ([staps-rooryck-2024] Table 1). -/
def construire : Verb :=
  transitive "construire" accomplishmentSubjectProfile creationObject .accomplishment

/-- *tuer* 'kill', whose object does not survive the event ([staps-rooryck-2024] Table 1). -/
def tuer : Verb :=
  transitive "tuer" accomplishmentSubjectProfile
    (insert .dependentExistence accomplishmentObjectProfile) .achievement

/-- *aimer* 'love', a stative psych verb ([staps-rooryck-2024] Table 1). -/
def aimer : Verb := transitive "aimer" experiencerProfile independentParticipant .state

/-- *adorer* 'adore, worship', a stative psych verb ([staps-rooryck-2024] §3.2). -/
def adorer : Verb := transitive "adorer" experiencerProfile independentParticipant .state

/-- *respecter* 'respect', a stative psych verb ([staps-rooryck-2024] Table 1). -/
def respecter : Verb := transitive "respecter" experiencerProfile independentParticipant .state

/-- *accompagner* 'accompany' ([staps-rooryck-2024] §3.2). -/
def accompagner : Verb :=
  transitive "accompagner" companionSubject independentParticipant .activity

/-- *suivre* 'follow' in its goal-directed sense, with a volitional subject
([staps-rooryck-2024] §3.3). -/
def suivreDyn : Verb :=
  transitive "suivre" activitySubjectProfile independentParticipant .activity

/-- *suivre* 'follow' in its stative positional sense, a purely spatial relation
([staps-rooryck-2024] §3.3). -/
def suivreStat : Verb :=
  transitive "suivre" independentParticipant independentParticipant .state .stative

/-- *précéder* 'precede' in its stative positional sense ([staps-rooryck-2024] §3.3). -/
def preceder : Verb :=
  transitive "précéder" independentParticipant independentParticipant .state

/-- *abandonner* 'abandon' in its telic sense, an event of leaving behind
([staps-rooryck-2024] §3.4, with examples from [authier-revuz-1972]). -/
def abandonner : Verb :=
  transitive "abandonner" accomplishmentSubjectProfile accomplishmentObjectProfile
    .accomplishment

/-- *abandonner* 'neglect' in its atelic stative sense ([staps-rooryck-2024] §3.4, with
examples from [authier-revuz-1972]). -/
def abandonnerStat : Verb :=
  transitive "abandonner" neglectSubject independentParticipant .state .stative

/-- *délaisser* 'leave behind' in its telic sense ([staps-rooryck-2024] §3.4). -/
def delaisser : Verb :=
  transitive "délaisser" accomplishmentSubjectProfile accomplishmentObjectProfile
    .accomplishment

/-- *délaisser* 'neglect' in its atelic stative sense ([staps-rooryck-2024] §3.4). -/
def delaisserStat : Verb :=
  transitive "délaisser" neglectSubject independentParticipant .state .stative

/-! ### Monadic verbs

The intransitive verbs of [grevisse-goosse-2008] §§812–813 and of [sorace-2000]'s French
examples. -/

/-- *aller* 'go', a verb of motion to a goal. -/
def aller : Verb where
  morphs := [.root "aller"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *arriver* 'arrive', a verb of motion to a goal. -/
def arriver : Verb where
  morphs := [.root "arriver"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *entrer* 'enter', a verb of motion to a goal. -/
def entrer : Verb where
  morphs := [.root "entrer"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *retourner* 'go back', a verb of motion to a goal. -/
def retourner : Verb where
  morphs := [.root "retourner"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *tomber* 'fall', a verb of motion in a direction. -/
def tomber : Verb where
  morphs := [.root "tomber"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *venir* 'come', a verb of motion to a goal. -/
def venir : Verb where
  morphs := [.root "venir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *partir* 'leave', a verb of motion from a source. -/
def partir : Verb where
  morphs := [.root "partir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .source

/-- *sortir* 'go out', a verb of motion from a source. -/
def sortir : Verb where
  morphs := [.root "sortir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .source

/-- *décéder* 'die', a change of state. -/
def deceder : Verb where
  morphs := [.root "décéder"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement

/-- *devenir* 'become', a change of state. -/
def devenir : Verb where
  morphs := [.root "devenir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement

/-- *mourir* 'die', a change of state. -/
def mourir : Verb where
  morphs := [.root "mourir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement

/-- *naître* 'be born', a change of state. -/
def naitre : Verb where
  morphs := [.root "naître"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement

/-- *rester* 'stay', the continuation of a state. -/
def rester : Verb where
  morphs := [.root "rester"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .state
  phasal := some .continuation

/-- *aboutir* 'succeed, end up', telic. -/
def aboutir : Verb where
  morphs := [.root "aboutir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .achievement

/-- *atterrir* 'land', telic. -/
def atterrir : Verb where
  morphs := [.root "atterrir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .achievement

/-- *disparaître* 'disappear', with *avoir* for the event, *Elle a disparu prématurément*, and, now
rarely, *être* for the state, *Il est aujourd'hui disparu*. -/
def disparaitre : Verb where
  morphs := [.root "disparaître"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .achievement

/-- *paraître* 'appear, come out'. -/
def paraitre : Verb where
  morphs := [.root "paraître"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .achievement

/-- *grandir* 'grow', a change along a scale of size. -/
def grandir : Verb where
  morphs := [.root "grandir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .accomplishment
  scaleDimension := some .generalSize

/-- *survivre* 'survive', stative. -/
def survivre : Verb where
  morphs := [.root "survivre"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}
  vendlerClass := some .state

/-- *exister* 'exist', stative. -/
def exister : Verb where
  morphs := [.root "exister"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}
  vendlerClass := some .state

/-- *travailler* 'work', an activity whose subject controls it. -/
def travailler : Verb where
  morphs := [.root "travailler"]
  valency := .ofFrame ArgumentFrame.intransitive [some activitySubjectProfile]
  perfectAuxiliaries := {.have}
  vendlerClass := some .activity

/-- *courir* 'run', a verb of manner of motion, which selects no directional phrase. -/
def courir : Verb where
  morphs := [.root "courir"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}
  vendlerClass := some .activity
  direction := some .place

/-- *nager* 'swim', a verb of manner of motion, which selects no directional phrase. -/
def nager : Verb where
  morphs := [.root "nager"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}
  vendlerClass := some .activity
  direction := some .place

/-! ### The perfect auxiliary

Each monadic entry records the auxiliaries of its perfect: *être* for the closed list of
[grevisse-goosse-2008] §812b, verbs "exprimant, pour la plupart, un mouvement ou un changement
d'état"; both for the verbs of §813a, *avoir* when they express the action and *être* when they
express the state that results; and *avoir* for the others (§811). -/

/-- In *Marie a couru jusqu'à la maison* ([sorace-2000] (42b)) the directional phrase is an
adjunct to *courir*, which it leaves as it is. -/
example : courir.withPath (.ofCase .ill) = courir := rfl

/-! ### Attitude verbs

The attitude verbs record the mood of the finite complement each selects in an affirmative
declarative clause. -/

/-- *vouloir* 'want' takes a *que* clause in the subjunctive and an infinitive under subject
control. -/
def vouloir : Verb where
  morphs := [.root "vouloir"]
  valency := .ofFrames [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
    (controllers := [none, some 0])
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- *espérer* 'hope' takes a *que* clause in the indicative and an infinitive under subject
control. Some speakers also accept the subjunctive in a complement about the future, a use this
entry does not cover. -/
def esperer : Verb where
  morphs := [.root "espérer"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
    (controllers := [none, some 0])
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- *croire* 'believe' takes a *que* clause in the indicative. -/
def croire : Verb where
  morphs := [.root "croire"]
  valency := .ofFrames [ArgumentFrame.finiteClause]
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)

/-- `allVerbs` lists the entries. -/
def allVerbs : List Verb :=
  [faire, laisser, vouloir, esperer, croire,
   brunir, noircir, palir, rajeunir, rougir, approcher, durcir, plier, radoucir, refroidir,
   laver, briser, ecrire, construire, tuer, aimer, adorer, respecter, accompagner,
   suivreDyn, suivreStat, preceder, abandonner, abandonnerStat, delaisser, delaisserStat,
   aller, arriver, entrer, retourner, tomber, venir, partir, sortir, deceder, devenir, mourir,
   naitre, rester, aboutir, atterrir, disparaitre, paraitre, grandir, survivre, exister,
   travailler, courir, nager]

theorem telic_or_continuation_of_perfectAuxiliaries_eq_be :
    ∀ v ∈ allVerbs, v.perfectAuxiliaries = {.be} →
      v.vendlerClass.map (·.telicity) = some .telic ∨ v.phasal = some .continuation := by
  decide

/-- Telicity does not bring *être* with it, since a telic verb of §813a takes *avoir* for the
action. -/
theorem exists_telic_and_have_mem :
    ∃ v ∈ allVerbs,
      .have ∈ v.perfectAuxiliaries ∧ v.vendlerClass.map (·.telicity) = some .telic := by
  decide

end French.Verbs
