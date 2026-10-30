module

public import Linglib.Fragments.English.Verbs.Implicative

/-!
# English attitude verbs

This file defines the English clause-embedding verbs of attitude: the factives *know*, *regret*,
*realize*, *discover* and *notice*, the doxastics *believe*, *think* and *doubt*, the
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
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree

/-! ### Factive / Semifactive -/

/-- "know" — factive, presupposes complement is true -/
def know : Verb where
  morphs := [.root "know"]
  past := "knew"
  pastPart := "known"
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  complementSig := some .mono
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  levinClasses := {LevinClass.conjecture}

/-- "regret" — emotive factive, presupposes complement is true -/
def regret : Verb where
  morphs := [.root "regret"]
  doubling := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  attitude := some (.preferential .negative true)
  factivity := some .full
  levinClasses := {LevinClass.admire}

/-- "realize" — factive, presupposes complement is true -/
def realize : Verb where
  morphs := [.root "realize"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .semi

/-- "discover" — semi-factive, weaker projection -/
def discover : Verb where
  morphs := [.root "discover"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  levinClasses := {LevinClass.conjecture, .sight}

/-- "notice" — semi-factive -/
def notice : Verb where
  morphs := [.root "notice"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  levinClasses := {LevinClass.see}

/-! ### Doxastic Attitude -/

/-- "believe" — doxastic attitude verb, creates opaque context. It is gradable, measuring the
holder's degree of certainty in the complement ([hawthorne-rothschild-spectre-2016];
[koev-2026] (3), (7)–(10)), and takes the maximizers *fully*, *completely* and *entirely* ((12)).
The fragment enters it on the confidence scale of *certain*, *sure* and *confident*. -/
def believe : Verb where
  morphs := [.root "believe"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  scaleDimension := some .confidence
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .doxastic)
  complementSig := some .mono
  levinClasses := {LevinClass.declare}

/-- "think" — doxastic attitude verb -/
def think : Verb where
  morphs := [.root "think"]
  past := "thought"
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.doxastic .doxastic)
  complementSig := some .mono
  levinClasses := {LevinClass.declare}

/-- "doubt" — doxastic attitude verb, the apparent antonym of *believe*, measuring certainty
towards the negative pole ([koev-2026] (17), fn. 7). Its complement is downward entailing, as its
licensing of negative polarity items shows. -/
def doubt : Verb where
  morphs := [.root "doubt"]
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
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.appoint, .want}

/-- *intend* reports an intention ([grano-2024]). Its subject controls its infinitive (*intend
    to leave*); its non-control *for*–*to* complement (*intend for Ben to come along*) is not
    entered. It rejects indicative complements cross-linguistically, as in the ungrammatical
    *Kim intends that Sandy leaves*, since it needs an eventuality abstract, `cause*` binding
    the complement's event argument. -/
def intend : Verb where
  morphs := [.root "intend"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.characterize}

/-- *decide* is a hybrid of belief and intention ([grano-2024], §6.1). With a nonfinite
    complement, which its subject controls, it reports forming an intention (*Kim decided to quit
    smoking*), and with a finite one forming a belief (*Kim decided that smoking is harmful*). The
    complement type determines the reading, as with Italian *convincere*
    ([fusco-sgrizzi-2026]). -/
def decide_ : Verb where
  morphs := [.root "decide"]
  valency := .ofFrames [ArgumentFrame.infinitival, ArgumentFrame.finiteClause]
    (controllers := [some 0])
  vendlerClass := some .achievement
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- *hope* is a preferential attitude verb that takes a finite clause (*hope that John leaves*)
    or an infinitive its subject controls (*hope to leave*). -/
def hope : Verb where
  morphs := [.root "hope"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
    (controllers := [none, some 0])
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.long}

/-- *pray* is a preferential attitude verb that permits future temporal orientation. Like
    *hope*, it can take a circumstantial modal base, allowing future-oriented readings under past
    tense morphology ([klecha-2016]). It takes a finite clause (*pray that God helps*) or an
    infinitive its subject controls (*pray to be saved*). -/
def pray : Verb where
  morphs := [.root "pray"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.infinitival]
    (controllers := [none, some 0])
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.long}

/-- "expect" — preferential attitude verb -/
def expect : Verb where
  morphs := [.root "expect"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- "wish" — preferential attitude verb -/
def wish : Verb where
  morphs := [.root "wish"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  levinClasses := {LevinClass.long}

/-- "fear" — a preferential attitude verb of Class 2, which takes questions. -/
def fear : Verb where
  morphs := [.root "fear"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative true)
  levinClasses := {LevinClass.admire, .marvel}

/-- "dread" — a preferential attitude verb of Class 2, which takes questions. -/
def dread : Verb where
  morphs := [.root "dread"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative true)
  levinClasses := {LevinClass.admire}

/-- "worry" — preferential attitude verb -/
def worry : Verb where
  morphs := [.root "worry"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .negative false)
  levinClasses := {LevinClass.amuse, .marvel}

/-! ### Clause-Embedding Predicates -/

/-! The 20 clause-embedding predicates of [degen-tonhauser-2022].
    Predicates already defined above: know, discover, see, think, say, hear.
    "be annoyed" and "be right" are copular constructions, not simple verbs. -/

/-- *reveal* is a communication verb that [degen-tonhauser-2022] find canonically factive. -/
def reveal : Verb where
  morphs := [.root "reveal"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  attitude := some (.doxastic .doxastic)
  factivity := some .full
  levinClasses := {LevinClass.characterize, .say}

/-- "acknowledge" — optionally factive communication verb
    Levin lists *acknowledge* only among the appoint verbs (§29.1), a different frame. -/
def acknowledge : Verb where
  morphs := [.root "acknowledge"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appoint}


/-- "admit" — optionally factive communication verb
    Levin lists *admit* among the conjecture verbs (§29.5). -/
def admit : Verb where
  morphs := [.root "admit"]
  doubling := true
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.conjecture}

/-- "announce" — communication verb -/
def announce : Verb where
  morphs := [.root "announce"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.say}

/-- "confess" — optionally factive communication verb -/
def confess : Verb where
  morphs := [.root "confess"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.declare, .say}

/-- "inform" — optionally factive communication verb with recipient -/
def inform : Verb where
  morphs := [.root "inform"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement

/-- "suggest" — non-factive communication verb -/
def suggest : Verb where
  morphs := [.root "suggest"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .achievement
  levinClasses := {LevinClass.reflexiveAppearance, .say}

/-- "pretend" — anti-veridical attitude verb -/
def pretend : Verb where
  morphs := [.root "pretend"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  opaqueContext := true

/-- "confirm" — evidential verb -/
def confirm : Verb where
  morphs := [.root "confirm"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.characterize}

/-- "demonstrate" — evidential verb -/
def demonstrate : Verb where
  morphs := [.root "demonstrate"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.transferOfMessage}

/-- "establish" — evidential verb -/
def establish : Verb where
  morphs := [.root "establish"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.characterize}

/-- "prove" — evidential verb -/
def prove : Verb where
  morphs := [.root "prove"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.declare}

/-! ### Question-Embedding -/

/-- "wonder" — embeds questions only -/
def wonder : Verb where
  morphs := [.root "wonder"]
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .state
  opaqueContext := true
  levinClasses := {LevinClass.marvel}

/-- "ask" — embeds questions -/
def ask : Verb where
  morphs := [.root "ask"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .achievement
  levinClasses := {LevinClass.transferOfMessage}

/-- "investigate" — rogative, embeds interrogatives only -/
def investigate : Verb where
  morphs := [.root "investigate"]
  valency := .ofFrames
    [ArgumentFrame.question, ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef)]
  vendlerClass := some .activity
  levinClasses := {LevinClass.investigate, .sight}

/-- *depend on* is a rogative predicate, embedding only interrogatives ([dayal-2025]). -/
def depend_on : Verb where
  morphs := [.root "depend", .free "on"]
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .state

/-- "remember" in factive/question-embedding sense. -/
def remember_rog : Verb where
  morphs := [.root "remember"]
  valency := .ofFrames [ArgumentFrame.finiteClause, ArgumentFrame.question]
  vendlerClass := some .state
  passivizable := false
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  senseTag := .rogative
  levinClasses := {LevinClass.characterize}

/-- "forget" in factive/question-embedding sense, with a finite clause, a PRO-ing gerund
(*John forgot having stopped by the flower shop*, [williams-2025] (8)) or a question. -/
def forget_rog : Verb where
  morphs := [.root "forget"]
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
