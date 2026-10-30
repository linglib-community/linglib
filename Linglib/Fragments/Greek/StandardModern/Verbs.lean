module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Modern Greek verbs

Clause-embedding verbs of Modern Greek, each with the coding of the complements it takes: an
indicative declarative clause, which *oti* or *pu* introduces, a polar question with *an*, or a
subjunctive clause with *na* (`Complementizers.lean`). The entries carry the attitude and
stativity metadata that [angelopoulos-2026]'s data turns on, and the volitional, intention and
causative verbs are those of [grano-2024]'s survey of mood choice, from
[giannakidou-mari-2021].

[angelopoulos-2026]'s own apparatus, the light-noun selection, the content and situation typing,
the attested selection classes and the stativity generalizations, lives in
`Studies/Angelopoulos2026.lean` as projections over these entries.

## References

* [angelopoulos-2026]
* [roussou-2010]
* [grano-2024]
* [giannakidou-mari-2021]
* [bondarenko-2022]
* [landau-2010]
-/

@[expose] public section

namespace Greek.StandardModern.Verbs

/-! ### Matrix verbs selecting *oti*

Verbs of saying / belief / knowledge / understanding
([angelopoulos-2026] ex. 1a, 3, 36). -/

/-- *léo* (λέω) 'say' — past tense *ípe* in [angelopoulos-2026]
    ex. 1a. Speech-act verb, eventive (activity). -/
def leo : Verb where
  morphs := [.root "léo"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  vendlerClass := some .activity

/-- *pistévo* (πιστεύω) 'believe' — doxastic, stative; the impersonal
    passive *pistévetai oti* is standard. -/
def pistevo : Verb where
  morphs := [.root "pistévo"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  vendlerClass := some .state
  opaqueContext := true

/-- *kséro* (ξέρω) 'know' (alongside *gnorízo*) — factive epistemic,
    stative. Rejects manner adverbs ([angelopoulos-2026] ex. 21a). -/
def ksero : Verb where
  morphs := [.root "kséro"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  vendlerClass := some .state

/-- *katalavéno* (καταλαβαίνω) 'understand' — eventive (allows
    manner adverbs in [angelopoulos-2026] ex. 21b),
    factive epistemic. -/
def katalaveno : Verb where
  morphs := [.root "katalavéno"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  vendlerClass := some .achievement

/-- *sinidhitopió* (συνειδητοποιώ) 'realize' — eventive (achievement),
    factive epistemic ([angelopoulos-2026] ex. 21b). -/
def sinidhitopio : Verb where
  morphs := [.root "sinidhitopió"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  vendlerClass := some .achievement

/-- *eksigó* (εξηγώ) 'explain' — accomplishment, takes *oti*
    yielding *explanans* reading ([angelopoulos-2026] ex. 4a). -/
def eksigo : Verb where
  morphs := [.root "eksigó"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .accomplishment

/-! ### Matrix verbs selecting *pu*

Emotive-factive predicates, stative under [angelopoulos-2026]'s §2.3
stativity restriction. -/

/-- *metanióno* (μετανιώνω) 'regret' — preferential (negative
    valence), stative. [angelopoulos-2026] ex. 1b, 20. -/
def metaniono : Verb where
  morphs := [.root "metanióno"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative true)
  vendlerClass := some .state

/-- *aréso* (αρέσω) 'appeal to / be liked by' — Class III experiencer,
    stative ([angelopoulos-2026] ex. 13, 14; [landau-2010]). -/
def areso : Verb where
  morphs := [.root "aréso"]
  valency := .ofFrame ({ ArgumentFrame.finiteClause with external := none })
  attitude := some (.preferential .positive true)
  vendlerClass := some .state

/-- *xérome* (χαίρομαι) 'be happy/glad' — preferential positive,
    stative. -/
def xerome : Verb where
  morphs := [.root "xérome"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .positive true)
  vendlerClass := some .state

/-! ### Verbs compatible with both *oti* and *pu*

Eventive with *oti*, stative with *pu* ([angelopoulos-2026] ex. 19,
22–23, fn. 16). Both complements are finite indicative clauses, so the
polysemy rides on sense-tagged entry pairs (`SenseTag.stative`, the
`suivreStat` pattern) rather than frame-keyed `Verb.readings` rows. -/

/-- *thimáme* (θυμάμαι) 'remember' — eventive attitude sense ('recall,
    infer that'), the one available with *oti* ([angelopoulos-2026]
    ex. 22, fn. 16); the stative direct-perception recollection sense
    is `thimameStat`. -/
def thimame : Verb where
  morphs := [.root "thimáme"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  vendlerClass := some .achievement

/-- *thimáme* — stative direct-perception recollection sense
    ('remember him reading'), the one available with *pu*
    ([angelopoulos-2026] fn. 16; [roussou-2010] ex. 17's strong
    presupposition). -/
def thimameStat : Verb where
  morphs := [.root "thimáme"]
  valency := .ofFrame ArgumentFrame.finiteClause
  senseTag := .stative
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  vendlerClass := some .state

/-- *thimóno* (θυμώνω) 'get angry' — eventive (achievement) sense, the
    one available with *oti*; the stative sense is `thimonoStat`
    ([angelopoulos-2026] ex. 19, 23). -/
def thimono : Verb where
  morphs := [.root "thimóno"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative true)
  vendlerClass := some .achievement

/-- *thimóno* — stative 'be angry' sense, the one available with *pu*
    ([angelopoulos-2026] ex. 19, 23). -/
def thimonoStat : Verb where
  morphs := [.root "thimóno"]
  valency := .ofFrame ArgumentFrame.finiteClause
  senseTag := .stative
  attitude := some (.preferential .negative true)
  vendlerClass := some .state

/-- *nomízo* (νομίζω) 'think' — doxastic, non-veridical, stative; takes *oti*, and *na*
    under matrix negation or question ([roussou-2010]). -/
def nomizo : Verb where
  morphs := [.root "nomízo"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .doxastic)
  vendlerClass := some .state
  opaqueContext := true

/-- *paradhéxome* (παραδέχομαι) 'admit' — factive speech-act verb; takes *oti* and not
    *pu* ([roussou-2010] (19a)). Roussou's factive *oti* complements carry what she calls a weak
    presupposition; the semi-factive class is our mapping of it. -/
def paradhexome : Verb where
  morphs := [.root "paradhéxome"]
  valency := .ofFrame ArgumentFrame.finiteClause
  speechActVerb := true
  attitude := some (.doxastic .doxastic)
  factivity := some .semi
  vendlerClass := some .achievement

/-- *antilamvánome* (αντιλαμβάνομαι) 'realize' — factive epistemic, eventive; takes *oti*
    and not *pu* ([roussou-2010]). -/
def antilamvanome : Verb where
  morphs := [.root "antilamvánome"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  vendlerClass := some .achievement

/-- *anisixó* (ανησυχώ) 'worry' — preferential (negative valence) experiencer verb,
    stative; takes *pu* on the factive reading and *oti* otherwise ([roussou-2010]). -/
def anisixo : Verb where
  morphs := [.root "anisixó"]
  valency := .ofFrame ArgumentFrame.finiteClause
  attitude := some (.preferential .negative true)
  vendlerClass := some .state

/-! ### Interrogative and volitional predicates -/

/-- *anarotjéme* (αναρωτιέμαι) 'wonder' — rogative, selecting the interrogative
    complementizer *an* ([roussou-2010]). -/
def anarotjeme : Verb where
  morphs := [.root "anarotjéme"]
  valency := .ofFrame ArgumentFrame.question
  vendlerClass := some .state
  senseTag := .rogative

/-- *thélo* (θέλω) 'want' — volitional, taking only a *na*-clause ([roussou-2010]). -/
def thelo : Verb where
  morphs := [.root "thélo"]
  valency := .ofFrame ({ complements := [.clausal (coding := some .subjunctive)] })
  attitude := some (.preferential .positive true)
  vendlerClass := some .state

/-- *elpízo* (ελπίζω) 'hope' — takes a *na*-clause or an *oti*-clause ([grano-2024],
    from [giannakidou-mari-2021]). -/
def elpizo : Verb where
  morphs := [.root "elpízo"]
  valency := .ofFrames
    [{ complements := [.clausal (coding := some .subjunctive)] }, ArgumentFrame.finiteClause]
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  vendlerClass := some .state

/-- *protítheme* (προτίθεμαι) 'intend' — takes only a *na*-clause ([grano-2024], from
    [giannakidou-mari-2021], in the third singular *protíthete*). -/
def protitheme : Verb where
  morphs := [.root "protítheme"]
  valency := .ofFrame ({ complements := [.clausal (coding := some .subjunctive)] })
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  vendlerClass := some .state

/-- *vázo* (βάζω) 'put', causative 'make' — takes an object and a *na*-clause
    ([grano-2024]). -/
def vazo : Verb where
  morphs := [.root "vázo"]
  valency := .ofFrame ({ complements := [.nominal, .clausal (coding := some .subjunctive)] })

/-! ### Occurrence verbs -/

/-- *simvéni* (συμβαίνει) 'happen/occur' — unaccusative achievement,
    the [angelopoulos-2026] ex. 34 diagnostic. Rejects both *oti*- and
    *pu*-complements and takes subjunctive *na*-clauses
    ([angelopoulos-2026] fn. 14). -/
def simveni : Verb where
  morphs := [.root "simvéni"]
  valency := .ofFrame
    { external := none, complements := [.clausal (coding := some .subjunctive)] }
  vendlerClass := some .achievement

end Greek.StandardModern.Verbs
