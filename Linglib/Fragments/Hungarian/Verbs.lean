module

public import Linglib.Syntax.Category.Verb.Basic

/-!
# Hungarian verbs

This file defines the Hungarian matrix predicates of Egressy's study of sequence of tense: the
perception, cognition, psychological and communication verbs that embed a finite *hogy*-clause
(*lát* 'see', *hall* 'hear', *álmodik* 'dream', *gondol* 'think', *hisz* 'believe', *aggaszt*
'worry', *mond* 'say', *rikolt* 'shout', *morog* 'growl') and the intransitives whose
*hogy*-clause is only an adjunct (*telefonál* 'call on the phone', *irigykedik* 'be jealous').
The case of the clause's expletive diagnoses its grammatical role, accusative *azt* an object,
nominative *az* a subject and instrumental *azzal* or *amiatt* 'because of it' an adjunct, so
*aggaszt* has the clause as its subject with an accusative experiencer, *morog* embeds it as a
complement or hosts it as an adjunct of its intransitive frame, and the intransitives give it no
position at all. A Hungarian verb agrees with the definiteness of its object as well as with its
subject, in the definite or the indefinite conjugation of the reference grammar, so a clausal
complement with the accusative expletive *azt* takes the definite form, *mondta* 'said it'.
Whether the complement reports speech or not is a property of the clause and not of the verb, as
Egressy shows with *hall* and *morog*, so the entries carry no clause type.

## Main definitions

* `Hungarian.Verbs.verbs`: the entries.

## References

* [egressy-2026]
* [kenesei-vago-fenyvesi-1998]
* [kiss-2002]
-/

@[expose] public section

namespace Hungarian.Verbs

open ArgumentStructure

/-- A Hungarian verb is the cross-linguistic `Verb` with the stem its past tense attaches to,
where that differs from the citation form: an ik-verb drops *-ik*, as *álmodik* ~ *álmod-t-a*,
and an sz-verb shows its t-stem allomorph, as *hisz* ~ *hi-tt-e*. An entry that lists none is
regular. -/
structure Verb extends _root_.Verb where
  /-- The past stem, where it is not the citation form. -/
  pastStem : Option String := none
  deriving BEq

/-- The stem the past tense attaches to. -/
def Verb.stem (v : Verb) : String := v.pastStem.getD v.toVerb.form

/-- *lát* 'see', a perception verb, transitive and embedding a finite clause. -/
def lat : Verb where
  morphs := [.root "lát"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.finiteClause, [0, 1])]
    [some perception.subjectProfile, none]
  vendlerClass := some .state
  attitude := some (.doxastic .veridical)
  factivity := some .semi

/-- *hall* 'hear', a perception verb that embeds a perceived event or a heard report alike. -/
def hall : Verb where
  morphs := [.root "hall"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.finiteClause, [0, 1])]
    [some perception.subjectProfile, none]
  vendlerClass := some .state

/-- *álmodik* 'dream'. -/
def almodik : Verb where
  morphs := [.root "álmodik"]
  valency := .ofFrame ArgumentFrame.finiteClause
  opaqueContext := true
  pastStem := some "álmod"

/-- *gondol* 'think', a doxastic attitude verb. -/
def gondol : Verb where
  morphs := [.root "gondol"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono

/-- *hisz* 'believe', a doxastic attitude verb. -/
def hisz : Verb where
  morphs := [.root "hisz"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .state
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)
  complementSig := some .mono
  pastStem := some "hi"

/-- *aggaszt* 'worry', a psychological verb whose clause is its nominative subject, beside an
accusative experiencer: *Az aggasztotta Petit, hogy ...* 'It worried Peti that ...'. -/
def aggaszt : Verb where
  morphs := [.root "aggaszt"]
  valency := .ofFrame ArgumentFrame.clausalSubject
  vendlerClass := some .state

/-- *mond* 'say'. -/
def mond : Verb where
  morphs := [.root "mond"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  speechActVerb := true

/-- *rikolt* 'shout', a manner-of-speaking verb. -/
def rikolt : Verb where
  morphs := [.root "rikolt"]
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  speechActVerb := true

/-- *morog* 'growl', a manner-of-speaking verb, basically an intransitive that hosts a reason
adjunct and derivedly complement-taking with the accusative expletive *azt*. -/
def morog : Verb where
  morphs := [.root "morog"]
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.finiteClause, [0, 1])]
  vendlerClass := some .activity
  speechActVerb := true

/-- *telefonál* 'call on the phone', an intransitive; a speech-reporting *hogy*-clause attaches
only as an adjunct with the instrumental expletive *azzal*. -/
def telefonal : Verb where
  morphs := [.root "telefonál"]
  valency := .ofFrame ArgumentFrame.intransitive
  vendlerClass := some .activity

/-- *irigykedik* 'be jealous', an intransitive with a reason-adjunct *hogy*-clause. -/
def irigykedik : Verb where
  morphs := [.root "irigykedik"]
  valency := .ofFrame ArgumentFrame.intransitive
  vendlerClass := some .state
  pastStem := some "irigyked"

/-- The entries. -/
def verbs : List Verb :=
  [lat, hall, almodik, gondol, hisz, aggaszt, mond, rikolt, morog, telefonal, irigykedik]

end Hungarian.Verbs
