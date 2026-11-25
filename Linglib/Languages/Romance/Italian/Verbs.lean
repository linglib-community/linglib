module

public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Linglib.Semantics.ArgumentStructure.Unaccusativity
public import Linglib.Syntax.Category.Complementizer.Basic
public import Linglib.Syntax.Voice.Basic

/-!
# Italian verbs

Italian introduces a finite complement clause with *che* and an infinitival one with the
prepositional complementizers *di* and *a*, or with no complementizer at all, as after *volere*
'want', *intendere* 'intend' and the causative *fare* 'make'. A verb chooses among *di* and
*a*, and some take both with a difference in meaning: *Marco ha convinto Gianni di avere un
figlio* 'Marco has convinced Gianni that he has a child' reports a belief, *Marco ha convinto
Gianni a avere un figlio* 'Marco has convinced Gianni to have a child' an intention, and
*pensare* 'think' alternates the same way. In its finite complement *volere* takes the
subjunctive, *Gianni vuole che Maria sia contenta* 'Gianni wants Maria to be happy', with the
indicative marginal for some speakers, and so does *sperare* 'hope'; *intendere* takes no finite
complement, and *fare* embeds a finite clause only as *fare sì che* with the subjunctive. A
verb's `clauseTypers` are the complementizers of the complements it takes, and its frames record
the coding of each complement. Fusco and Sgrizzi's analysis of the *di* and *a* alternation is
`Studies/FuscoSgrizzi2026.lean`; the twelve transitive verbs of Palmieri's Appendix A that also
read reciprocally without *si* are ordinary entries here, and Palmieri's list of them is
`Studies/Palmieri2024.lean`.

The perfect is formed with the auxiliary *avere* 'have' or *essere* 'be' and the past participle
(`Italian.Verbs.auxiliary`). *Avere* is the auxiliary of every transitive verb. A verb formed with
a clitic reflexive pronoun takes *essere*, in its reflexive, reciprocal, indefinite personal and
passive uses alike (`Italian.Verbs.reflexiveAuxiliary`): *Si è tagliata* 'she cut herself', but
*Ha disprezzato se stessa* 'she despised herself' with the stressed pronoun.

An intransitive verb forms its perfect with *essere* when it expresses a change of location,
state or condition, the continuation of a state or existence in a state, and with *avere* when an
activity is in the foreground, whether or not its subject controls it
(`Italian.Verbs.perfectAuxiliary`): *Maria è arrivata* 'Maria has arrived' but *Mario ha
tossito* 'Mario has coughed'. *Correre* 'run' takes *essere* with a phrase that brings it to an
endpoint, *È corso al campo sportivo in un'ora* 'he ran to the sports ground in an hour', and
*nuotare* 'swim', which selects no such phrase, keeps *avere*.

## Implementation notes

The mood and complementizer facts of the attitude and causative entries are Grano's and Fusco
and Sgrizzi's. Grano treats *volere* 'want', *sperare* 'hope' and *intendere* 'intend' as desire
predicates, the last with a causative component the other two lack; the entries give all three
the preferential attitude of [anand-hacquard-2013]'s classification and do not record that
difference.

The passive is possible with every transitive verb but a few that denote a relation, *avere*
among them, and with a finite complement clause as object it is nearly always possible
([renzi-1988] ch. I §4.2). A sentence with a restructuring infinitive passivizes the infinitive
and not the governing verb, *Questa parete deve essere ridipinta* and not **è dovuta
ridipingere*, and the modals *volere*, *potere*, *dovere* and *sapere* are restructuring verbs.
`Italian.Verbs.HasPassive` is the rule on a frame, and an entry records what the grammar says of
the verb itself (`Verb.voices`): the passive is excluded for *avere* on its transitive frame and
for *volere* on its infinitive, and possible for the causative *fare*. An entry the grammar does
not name records nothing, and the grammar's marginal cases, as *sapere* 'know' with a finite
clause, are not recorded.

## References

* [fusco-sgrizzi-2026]
* [grano-2024]
* [anand-hacquard-2013]
* [renzi-1988]
* [palmieri-2024]
* [maiden-robustelli-2007]
* [sorace-2000]
* [levin-hovav-1995]
-/

@[expose] public section

namespace Italian

/-- An Italian verb is a verb entry with the clause-typers of the complements it takes, which its
frames cannot record, since *di* and *a* both introduce an infinitive. -/
structure Verb extends _root_.Verb where
  /-- The complementizers of the verb's complements; a bare infinitive contributes none. -/
  clauseTypers : List Complementizer := []

/-- The predicate the entry `v` forms with a path phrase of reading `p`. -/
def Verb.withPath (v : Verb) (p : Locative) : Verb :=
  { v with toVerb := v.toVerb.withPath p }

@[simp] theorem Verb.toVerb_withPath (v : Verb) (p : Locative) :
    (v.withPath p).toVerb = v.toVerb.withPath p := rfl

end Italian

open Verb (PerfectAuxiliary)

namespace Italian.Verbs

open ArgumentStructure

/-! ### Voice -/

/-- The passive of a frame with the auxiliary *essere* and the past participle. -/
def passive (fr : ArgumentFrame := .np) : Voice := (Voice.passive fr).marked [.free "essere"]

/-! ### Clause-typers -/

/-- *che* introduces a finite complement clause, indicative or subjunctive. -/
def che : Complementizer where
  morphs := [.free "che"]
  types := {.declarative}

/-- *di* introduces an infinitival complement. -/
def di : Complementizer where
  morphs := [.free "di"]
  coding := {.infinitive}

/-- *a* introduces an infinitival complement. -/
def a : Complementizer where
  morphs := [.free "a"]
  coding := {.infinitive}

/-! ### Attitude and causative verbs -/

/-- *convincere* 'convince' takes an infinitive with *di*, which reports a belief and allows
subject or object control, and one with *a*, which reports an intention and allows object
control only. -/
def convincere : Verb where
  morphs := [.root "convincere"]
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)
  opaqueContext := true
  clauseTypers := [di, a]

/-- *pensare* 'think' takes an infinitive with *di* or with *a*, with the same difference in
meaning as *convincere*. -/
def pensare : Verb where
  morphs := [.root "pensare"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  opaqueContext := true
  clauseTypers := [di, a]

/-- *volere* 'want' takes a *che* clause in the subjunctive, the indicative being marginal for
some speakers, and a bare infinitive under subject control, with which it is a modal verb and
does not itself take the passive form ([renzi-1988] ch. I §4.2.3). -/
def volere : Verb where
  morphs := [.root "volere"]
  valency := .ofFrames [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
    (controllers := [none, some 0])
  voices := [(passive ArgumentFrame.infinitival, .excluded)]
  opaqueContext := true
  attitude := some (.preferential .positive)
  clauseTypers := [che]

/-- *sperare* 'hope' takes a *che* clause in the subjunctive, the indicative being marginal for
some speakers. -/
def sperare : Verb where
  morphs := [.root "sperare"]
  valency := .ofFrame ArgumentFrame.subjunctiveClause
  opaqueContext := true
  attitude := some (.preferential .positive)
  clauseTypers := [che]

/-- *intendere* 'intend' takes a bare infinitive under subject control and no finite complement,
in either mood; the periphrasis *avere intenzione di* takes the infinitive with *di*. -/
def intendere : Verb where
  morphs := [.root "intendere"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- The causative *fare* 'make' takes a bare infinitive under object control, and a finite clause
only as *fare sì che* with the subjunctive, never the indicative. The passive of the causative
construction is always possible, *Questi libri erano fatti leggere a tutti* ([renzi-1988] ch. I
§4.2.3). -/
def fare : Verb where
  morphs := [.root "fare"]
  valency := .of
    [(ArgumentFrame.infinitival.withObject, [0, 2, 1]), (ArgumentFrame.subjunctiveClause, [0, 1])]
    (controllers := [some 2])
  voices := [(passive ArgumentFrame.infinitival.withObject, .optional)]
  clauseTypers := [che]

/-! ### Transitive verbs with a lexical reciprocal use -/

/-- *abbracciare* 'hug' is transitive and has a lexical reciprocal use. -/
def abbracciare : Verb where
  morphs := [.root "abbracciare"]
  valency := .ofFrame ArgumentFrame.np

/-- *baciare* 'kiss' is transitive and has a lexical reciprocal use. -/
def baciare : Verb where
  morphs := [.root "baciare"]
  valency := .ofFrame ArgumentFrame.np

/-- *coccolare* 'cuddle' is transitive and has a lexical reciprocal use. -/
def coccolare : Verb where
  morphs := [.root "coccolare"]
  valency := .ofFrame ArgumentFrame.np

/-- *conoscere* 'know (of)' is transitive and has a lexical reciprocal use. -/
def conoscere : Verb where
  morphs := [.root "conoscere"]
  valency := .ofFrame ArgumentFrame.np

/-- *consultare* 'consult, confer' is transitive and has a lexical reciprocal use. -/
def consultare : Verb where
  morphs := [.root "consultare"]
  valency := .ofFrame ArgumentFrame.np

/-- *frequentare* 'date' is transitive and has a lexical reciprocal use. -/
def frequentare : Verb where
  morphs := [.root "frequentare"]
  valency := .ofFrame ArgumentFrame.np

/-- *incontrare* 'meet' is transitive and has a lexical reciprocal use. -/
def incontrare : Verb where
  morphs := [.root "incontrare"]
  valency := .ofFrame ArgumentFrame.np

/-- *incrociare* 'cross, run into' is transitive and has a lexical reciprocal use. -/
def incrociare : Verb where
  morphs := [.root "incrociare"]
  valency := .ofFrame ArgumentFrame.np

/-- *lasciare* 'leave, break up with' is transitive and has a lexical reciprocal use. -/
def lasciare : Verb where
  morphs := [.root "lasciare"]
  valency := .ofFrame ArgumentFrame.np

/-- *sposare* 'marry' is transitive and has a lexical reciprocal use. -/
def sposare : Verb where
  morphs := [.root "sposare"]
  valency := .ofFrame ArgumentFrame.np

/-- *trovare* 'find, meet' is transitive and has a lexical reciprocal use. -/
def trovare : Verb where
  morphs := [.root "trovare"]
  valency := .ofFrame ArgumentFrame.np

/-- *vedere* 'see, meet' is transitive and has a lexical reciprocal use. -/
def vedere : Verb where
  morphs := [.root "vedere"]
  valency := .ofFrame ArgumentFrame.np

/-! ### The auxiliaries of the perfect -/

/-- *avere* 'have', the auxiliary of the perfect of transitive verbs and of intransitive verbs
of activity. As a transitive verb it denotes a relation and has no passive ([renzi-1988] ch. I
§4.2.1). -/
def avere : Verb where
  morphs := [.root "avere"]
  valency := .ofFrame ArgumentFrame.np
  perfectAuxiliaries := {.have}
  voices := [(passive, .excluded)]

/-- *essere* 'be', the auxiliary of the perfect of verbs of change and of state and of verbs
with a clitic reflexive pronoun. -/
def essere : Verb where
  morphs := [.root "essere"]
  valency := .ofFrame ArgumentFrame.intransitive [some {.independentExistence}]
  perfectAuxiliaries := {.be}

/-- The verb that forms the perfect with each auxiliary. -/
def auxiliary : PerfectAuxiliary → Verb
  | .have => avere
  | .be => essere

/-- A verb formed with a clitic reflexive pronoun takes *essere*, in its reflexive, reciprocal,
indefinite personal and passive uses ([maiden-robustelli-2007] §14.20). -/
def reflexiveAuxiliary : PerfectAuxiliary := .be

/-! ### Transitive verbs and verbs with a prepositional object -/

/-- *lavare* 'wash' is transitive. -/
def lavare : Verb where
  morphs := [.root "lavare"]
  valency := .ofFrame ArgumentFrame.np
  perfectAuxiliaries := {.have}

/-- *mangiare* 'eat' is transitive. -/
def mangiare : Verb where
  morphs := [.root "mangiare"]
  valency := .ofFrame ArgumentFrame.np
  perfectAuxiliaries := {.have}

/-- *rispondere* 'answer', an activity whose subject controls it, with the person answered in
a phrase with *a*. -/
def rispondere : Verb where
  morphs := [.root "rispondere"]
  valency := .ofFrame ArgumentFrame.intransitive [some activitySubjectProfile]
  perfectAuxiliaries := {.have}

/-! ### Monadic verbs

The monadic verbs of [sorace-2000]'s Italian examples, with the auxiliaries of their perfect,
both for the verbs [maiden-robustelli-2007] §14.20 lists as taking either. -/

/-- *venire* 'come', a verb of change of location. -/
def venire : Verb where
  morphs := [.root "venire"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  direction := some .goal

/-- *arrivare* 'arrive', a verb of change of location. -/
def arrivare : Verb where
  morphs := [.root "arrivare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  direction := some .goal

/-- *cadere* 'fall', a verb of change with a direction ([levin-hovav-1995] p. 147). -/
def cadere : Verb where
  morphs := [.root "cadere"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  direction := some .goal

/-- *salire* 'go up', a change along a scale of height. -/
def salire : Verb where
  morphs := [.root "salire"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  scaleDimension := some .height

/-- *marcire* 'go off, rot', a verb of change of state. -/
def marcire : Verb where
  morphs := [.root "marcire"]
  valency := .ofFrame ArgumentFrame.intransitive [some {.changeOfState, .causallyAffected}]
  perfectAuxiliaries := {.be}

/-- *fiorire* 'bloom', a verb of change of state. -/
def fiorire : Verb where
  morphs := [.root "fiorire"]
  valency := .ofFrame ArgumentFrame.intransitive [some {.changeOfState, .causallyAffected}]
  perfectAuxiliaries := {.be}

/-- *rimanere* 'remain', the persistence of a state. -/
def rimanere : Verb where
  morphs := [.root "rimanere"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  phasal := some .continuation

/-- *durare* 'last', which takes *essere* for the permanence of a state and *avere* where the
duration is in the foreground. -/
def durare : Verb where
  morphs := [.root "durare"]
  valency := .ofFrame ArgumentFrame.intransitive [some {.independentExistence}]
  perfectAuxiliaries := {.be, .have}

/-- *esistere* 'exist', existence in a state. -/
def esistere : Verb where
  morphs := [.root "esistere"]
  valency := .ofFrame ArgumentFrame.intransitive [some {.independentExistence}]
  perfectAuxiliaries := {.be}

/-- *bastare* 'be enough', existence in a state. -/
def bastare : Verb where
  morphs := [.root "bastare"]
  valency := .ofFrame ArgumentFrame.intransitive [some {.independentExistence}]
  perfectAuxiliaries := {.be}

/-- *sembrare* 'seem', a state predicated of the subject. -/
def sembrare : Verb where
  morphs := [.root "sembrare"]
  valency := .ofFrame ArgumentFrame.intransitive [some ∅]
  perfectAuxiliaries := {.be}

/-- *appartenere* 'belong', which takes *essere* for a state, *L'anello era appartenuto alla regina
Vittoria*, and *avere* where the subject controls it, *Non ho mai appartenuto al PCI*. -/
def appartenere : Verb where
  morphs := [.root "appartenere"]
  valency := .ofFrame ArgumentFrame.intransitive [some {.independentExistence}]
  perfectAuxiliaries := {.be, .have}

/-- *lavorare* 'work', an activity whose subject controls it. -/
def lavorare : Verb where
  morphs := [.root "lavorare"]
  valency := .ofFrame ArgumentFrame.intransitive [some activitySubjectProfile]
  perfectAuxiliaries := {.have}

/-- *chiacchierare* 'chat', an activity whose subject controls it. -/
def chiacchierare : Verb where
  morphs := [.root "chiacchierare"]
  valency := .ofFrame ArgumentFrame.intransitive [some activitySubjectProfile]
  perfectAuxiliaries := {.have}

/-- *correre* 'run', a verb of manner of motion that selects a directional phrase. -/
def correre : Verb where
  morphs := [.root "correre"]
  valency := .ofFrames [ArgumentFrame.intransitive, ArgumentFrame.spatialPP]
  perfectAuxiliaries := {.be, .have}
  direction := some .place

/-- *saltare* 'jump', a verb of manner of motion that selects a directional phrase. -/
def saltare : Verb where
  morphs := [.root "saltare"]
  valency := .ofFrames [ArgumentFrame.intransitive, ArgumentFrame.spatialPP]
  perfectAuxiliaries := {.be, .have}
  direction := some .place

/-- *nuotare* 'swim', a verb of manner of motion that selects no directional phrase. -/
def nuotare : Verb where
  morphs := [.root "nuotare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}
  direction := some .place

/-- *tossire* 'cough', an activity whose subject does not control it. -/
def tossire : Verb where
  morphs := [.root "tossire"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}

/-- *squillare* 'ring', an activity whose subject does not control it. -/
def squillare : Verb where
  morphs := [.root "squillare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}

/-- `allVerbs` lists the entries. -/
def allVerbs : List Verb :=
  [convincere, pensare, volere, sperare, intendere, fare,
   abbracciare, baciare, coccolare, conoscere, consultare, frequentare, incontrare, incrociare,
   lasciare, sposare, trovare, vedere,
   avere, essere, lavare, mangiare, rispondere,
   venire, arrivare, cadere, salire, marcire, fiorire, rimanere, durare, esistere, bastare,
   sembrare, appartenere, lavorare, chiacchierare, correre, saltare, nuotare, tossire, squillare]

/-! ### The perfect auxiliary -/

/-- The auxiliary of the perfect of `v` on the frame `fr` without a clitic reflexive pronoun, with
a path phrase `p` if there is one ([maiden-robustelli-2007] §14.20), is *avere* for a transitive
verb. For an intransitive one it is
*essere* when the verb expresses a change of location, the continuation of a state or a change
along a scale, when the entry records a subject that neither acts volitionally nor causes, as the
subject of a change of state or of a state is, and when a phrase the verb selects brings it to an
endpoint; and *avere* otherwise, where an activity is in the foreground. -/
def perfectAuxiliary (v : Verb) (fr : ArgumentFrame)
    (p : Option Locative := none) : PerfectAuxiliary :=
  if fr.HasNominal then .have
  else if (∃ d ∈ v.direction, d ≠ .place) ∨ v.phasal = some .continuation ∨
      v.scaleDimension.isSome ∨
      (∃ θ ∈ v.slotProfile? .external, .volition ∉ θ ∧ .causation ∉ θ) ∨
      v.TakesSpatial ∧ ∃ r ∈ p, r.mode.IsBounded then .be
  else .have

theorem perfectAuxiliary_mem : ∀ v ∈ allVerbs, v.perfectAuxiliaries.Nonempty →
    perfectAuxiliary v (v.valency.frames.headD .intransitive) ∈ v.perfectAuxiliaries := by
  decide

/-- *Correre* takes *essere* with a phrase that brings it to an endpoint and *avere* with *verso*
'towards', while *nuotare* keeps *avere* (§14.20). -/
example :
    perfectAuxiliary correre .intransitive (some (.ofCase .ill)) = .be ∧
    perfectAuxiliary correre .intransitive (some { mode := .directional .approximative }) = .have ∧
    perfectAuxiliary nuotare .intransitive (some (.ofCase .ill)) = .have := by
  decide

/-- The passive is possible on a frame whose object is a noun phrase or a finite clause
([renzi-1988] ch. I §4.2). -/
def HasPassive (fr : ArgumentFrame) : Prop :=
  ∃ p ∈ fr.complements.head?, p.IsNominal ∨ p.IsFinite

instance : DecidablePred HasPassive := fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem hasPassive_of_voices : ∀ v ∈ allVerbs, ∀ fr ∈ v.valency.frames,
    v.voices.lookup (passive fr) = some .optional → HasPassive fr := by
  decide

/-- The verbs with no passive on a frame the rule covers are the verbs of relation, of which
the entries have *avere* (§4.2.1). -/
theorem filter_excluded_eq :
    (allVerbs.filter fun v ↦ ∃ fr ∈ v.valency.frames,
      HasPassive fr ∧ v.voices.lookup (passive fr) = some .excluded).map (·.morphs) =
        [avere.morphs] := by
  decide

/-- *Fare* has the passive on its causative frame, *volere* has none on its infinitive, which
the rule does not cover, and of *lavare* the grammar says nothing. -/
example :
    fare.voices.lookup (passive ArgumentFrame.infinitival.withObject) = some .optional ∧
      volere.voices.lookup (passive ArgumentFrame.infinitival) = some .excluded ∧
      ¬ HasPassive ArgumentFrame.infinitival ∧ lavare.voices.lookup passive = none := by
  decide

end Italian.Verbs
