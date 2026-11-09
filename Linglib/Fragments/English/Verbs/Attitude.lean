module

public import Linglib.Fragments.English.Verbs.Implicative

/-!
# English attitude verbs

This file defines the English clause-embedding verbs of attitude: the factives *know*, *regret*,
*resent*, *realize*, *discover* and *notice*, the doxastics *believe*, *think* and *doubt*, the
preferentials *want*, *intend*, *decide*, *hope*, *pray*, *expect*, *wish*, *fear*, *dread* and
*worry*, the clause-embedding predicates of Degen and Tonhauser's experiments, and the
question-embedding *wonder*, *ask*, *investigate* and *depend on* with the rogative senses of
*remember* and *forget*.

## References

* [dayal-2025]
* [degen-tonhauser-2022]
* [fusco-sgrizzi-2026]
* [grano-2024]
* [klecha-2016]
* [hawthorne-rothschild-spectre-2016]
* [koev-2026]
* [kiparsky-kiparsky-1970]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Data.VerbClasses

/-! ### Factive / Semifactive -/

/-- "know" — factive, presupposes complement is true -/
def know : Verb where
  morphs := [.root "know"]
  levin := some Levin1993.Index.know
  past := "knew"
  pastPart := "known"
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  complementSig := some .mono
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-- "regret" — emotive factive, presupposes complement is true -/
def regret : Verb where
  morphs := [.root "regret"]
  levin := some Levin1993.Index.regret
  doubling := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  attitude := some (.preferential .negative)
  factivity := some .full

/-- "resent" — emotive factive, presupposes complement is true ([kiparsky-kiparsky-1970]) -/
def resent : Verb where
  morphs := [.root "resent"]
  levin := some Levin1993.Index.resent
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  attitude := some (.preferential .negative)
  factivity := some .full

/-- "realize" — factive, presupposes complement is true -/
def realize : Verb where
  morphs := [.root "realize"]
  levin := none
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-- "discover" — semi-factive, weaker projection -/
def discover : Verb where
  morphs := [.root "discover"]
  levin := some Levin1993.Index.discover
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-- "notice" — semi-factive -/
def notice : Verb where
  morphs := [.root "notice"]
  levin := some Levin1993.Index.notice
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-! ### Doxastic Attitude -/

/-- "believe" — doxastic attitude verb, creates opaque context. It is gradable, measuring the
holder's degree of certainty in the complement ([hawthorne-rothschild-spectre-2016];
[koev-2026] (3), (7)–(10)), and takes the maximizers *fully*, *completely* and *entirely* ((12)).
The fragment enters it on the confidence scale of *certain*, *sure* and *confident*. Besides a
finite clause it takes an infinitive whose subject it raises to its object, an object that is no
participant of its own (*believe Julia to be a princess*; [noonan-2007] §2.2). -/
def believe : Verb where
  morphs := [.root "believe"]
  levin := some Levin1993.Index.believe
  valency := .ofLinks
    [(.finiteClause, [some 0, some 1]), (toInfinitive.withObject, [some 0, none, some 1])]
    (controls := [none, some (.complement 0)])
  vendlerClass := some .state
  scaleDimension := some .confidence
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .doxastic)
  complementSig := some .mono

/-- "think" — doxastic attitude verb -/
def think : Verb where
  morphs := [.root "think"]
  levin := some Levin1993.Index.think
  past := "thought"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .doxastic)
  complementSig := some .mono

/-- "doubt" — doxastic attitude verb, the apparent antonym of *believe*, measuring certainty
towards the negative pole ([koev-2026] (17), fn. 7). Its complement is downward entailing, as its
licensing of negative polarity items shows. -/
def doubt : Verb where
  morphs := [.root "doubt"]
  levin := none
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  scaleDimension := some .confidence
  scalePolarity := .negative
  opaqueContext := true
  attitude := some (.doxastic .doxastic)
  complementSig := some .anti

/-! ### Preferential Attitude -/

/-- "want" — preferential attitude verb with infinitival complement -/
def want : Verb where
  morphs := [.root "want"]
  levin := some Levin1993.Index.want
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- *intend* reports an intention ([grano-2024]). Its subject controls its infinitive (*intend
    to leave*); its non-control *for*–*to* complement (*intend for Ben to come along*) is not
    entered. It rejects indicative complements cross-linguistically, as in the ungrammatical
    *Kim intends that Sandy leaves*, since it needs an eventuality abstract, `cause*` binding
    the complement's event argument. -/
def intend : Verb where
  morphs := [.root "intend"]
  levin := some Levin1993.Index.intend
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- *decide* is a hybrid of belief and intention ([grano-2024], §6.1). With a nonfinite
    complement, which its subject controls, it reports forming an intention (*Kim decided to quit
    smoking*), and with a finite one forming a belief (*Kim decided that smoking is harmful*). The
    complement type determines the reading, as with Italian *convincere*
    ([fusco-sgrizzi-2026]). -/
def decide_ : Verb where
  morphs := [.root "decide"]
  levin := none
  valency := .ofFrames [toInfinitive, ArgumentFrame.finiteClause]
    (controllers := [some 0])
  vendlerClass := some .achievement
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- *hope* is a preferential attitude verb that takes a finite clause (*hope that John leaves*)
    or an infinitive its subject controls (*hope to leave*). -/
def hope : Verb where
  morphs := [.root "hope"]
  levin := some Levin1993.Index.hope
  valency := .ofFrames [ArgumentFrame.finiteClause, toInfinitive]
    (controllers := [none, some 0])
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- *pray* is a preferential attitude verb that permits future temporal orientation. Like
    *hope*, it can take a circumstantial modal base, allowing future-oriented readings under past
    tense morphology ([klecha-2016]). It takes a finite clause (*pray that God helps*) or an
    infinitive its subject controls (*pray to be saved*). -/
def pray : Verb where
  morphs := [.root "pray"]
  levin := some Levin1993.Index.pray
  valency := .ofFrames [ArgumentFrame.finiteClause, toInfinitive]
    (controllers := [none, some 0])
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- "expect" — preferential attitude verb, taking a finite clause, an infinitive its subject
controls (*expect to win*), or one whose subject it raises to its object (*expect the bridge to
collapse*). -/
def expect : Verb where
  morphs := [.root "expect"]
  levin := none
  valency := .ofLinks
    [(.finiteClause, [some 0, some 1]), (toInfinitive, [some 0, some 1]),
      (toInfinitive.withObject, [some 0, none, some 1])]
    (controls := [none, some .external, some (.complement 0)])
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- "wish" — preferential attitude verb -/
def wish : Verb where
  morphs := [.root "wish"]
  levin := some Levin1993.Index.wish
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- "fear" — a preferential attitude verb that takes questions. -/
def fear : Verb where
  morphs := [.root "fear"]
  levin := some Levin1993.Index.fear
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative)

/-- "dread" — a preferential attitude verb that takes questions. -/
def dread : Verb where
  morphs := [.root "dread"]
  levin := some Levin1993.Index.dread
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative)

/-- "worry" — preferential attitude verb -/
def worry : Verb where
  morphs := [.root "worry"]
  levin := some Levin1993.Index.worry
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative)

/-! ### Clause-Embedding Predicates -/

/-! The 20 clause-embedding predicates of [degen-tonhauser-2022].
    Predicates already defined above: know, discover, see, think, say, hear.
    "be annoyed" and "be right" are copular constructions, not simple verbs. -/

/-- *reveal* is a communication verb that [degen-tonhauser-2022] find canonically factive. -/
def reveal : Verb where
  morphs := [.root "reveal"]
  levin := some Levin1993.Index.reveal
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  attitude := some (.doxastic .doxastic)
  factivity := some .full

/-- "acknowledge" — optionally factive communication verb
    Levin lists *acknowledge* only among the appoint verbs (§29.1), a different frame. -/
def acknowledge : Verb where
  morphs := [.root "acknowledge"]
  levin := some Levin1993.Index.acknowledge
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement


/-- "admit" — optionally factive communication verb
    Levin lists *admit* among the conjecture verbs (§29.5). -/
def admit : Verb where
  morphs := [.root "admit"]
  levin := some Levin1993.Index.admit
  doubling := true
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement

/-- "announce" — communication verb -/
def announce : Verb where
  morphs := [.root "announce"]
  levin := some Levin1993.Index.announce
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement

/-- "confess" — optionally factive communication verb -/
def confess : Verb where
  morphs := [.root "confess"]
  levin := some Levin1993.Index.confess
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement

/-- "inform" — optionally factive communication verb with recipient -/
def inform : Verb where
  morphs := [.root "inform"]
  levin := none
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement

/-- "suggest" — non-factive communication verb -/
def suggest : Verb where
  morphs := [.root "suggest"]
  levin := some Levin1993.Index.suggest
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement

/-- "pretend" — anti-veridical attitude verb -/
def pretend : Verb where
  morphs := [.root "pretend"]
  levin := none
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  opaqueContext := true

/-- "confirm" — evidential verb -/
def confirm : Verb where
  morphs := [.root "confirm"]
  levin := some Levin1993.Index.confirm
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement

/-- "demonstrate" — evidential verb -/
def demonstrate : Verb where
  morphs := [.root "demonstrate"]
  levin := some Levin1993.Index.demonstrate
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement

/-- "establish" — evidential verb -/
def establish : Verb where
  morphs := [.root "establish"]
  levin := some Levin1993.Index.establish
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement

/-- "prove" — evidential verb -/
def prove : Verb where
  morphs := [.root "prove"]
  levin := some Levin1993.Index.prove
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement

/-! ### Question-Embedding -/

/-- "wonder" — embeds questions only -/
def wonder : Verb where
  morphs := [.root "wonder"]
  levin := some Levin1993.Index.wonder
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .state
  opaqueContext := true

/-- "ask" — embeds questions -/
def ask : Verb where
  morphs := [.root "ask"]
  levin := some Levin1993.Index.ask
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .achievement

/-- "investigate" — rogative, embeds interrogatives only -/
def investigate : Verb where
  morphs := [.root "investigate"]
  levin := some Levin1993.Index.investigate
  valency := .ofFrames
    [ArgumentFrame.question, ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef)]
  vendlerClass := some .activity

/-- *depend on* is a rogative predicate, embedding only interrogatives ([dayal-2025]). -/
def depend_on : Verb where
  morphs := [.root "depend", .free "on"]
  levin := none
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .state

/-- "remember" in factive/question-embedding sense. -/
def remember_rog : Verb where
  morphs := [.root "remember"]
  levin := some Levin1993.Index.remember
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  senseTag := .rogative

/-- "forget" in factive/question-embedding sense, with a finite clause, a PRO-ing gerund
(*John forgot having stopped by the flower shop*, [williams-2025] (8)) or a question. -/
def forget_rog : Verb where
  morphs := [.root "forget"]
  levin := none
  past := "forgot"
  pastPart := "forgotten"
  doubling := true
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.gerund, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .full
  senseTag := .rogative

end English.Verbs
