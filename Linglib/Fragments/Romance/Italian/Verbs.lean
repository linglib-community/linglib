module

public import Linglib.Semantics.ArgumentStructure.AuxiliarySelection
public import Linglib.Syntax.Category.Complementizer.Basic

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

An intransitive verb forms its perfect with *essere* when it expresses a change of location,
state or condition, the continuation of a state or existence in a state, and with *avere* when an
activity is in the foreground, whether or not its subject controls it
(`Italian.Verbs.perfectAuxiliary`): *Maria è arrivata* 'Maria has arrived' but *Mario ha
tossito* 'Mario has coughed'. *Correre* 'run' takes *essere* with a phrase that brings it to an
endpoint, *È corso al campo sportivo in un'ora* 'he ran to the sports ground in an hour', and
*nuotare* 'swim', which selects no such phrase, keeps *avere*.

## Implementation notes

The mood and complementizer facts of the attitude and causative entries are Grano's and Fusco
and Sgrizzi's; the attitude classifications and the non-passivizability of *volere*, *sperare*
and *intendere* are carried over from the earlier entries and are not in those sources.

## References

* [fusco-sgrizzi-2026]
* [grano-2024]
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
def Verb.withPath (v : Verb) (p : Adposition.SpatialReading) : Verb :=
  { v with toVerb := v.toVerb.withPath p }

@[simp] theorem Verb.toVerb_withPath (v : Verb) (p : Adposition.SpatialReading) :
    (v.withPath p).toVerb = v.toVerb.withPath p := rfl

end Italian

open Verb (PerfectAuxiliary)

namespace Italian.Verbs

open ArgumentStructure

/-! ### Clause-typers -/

/-- *che* introduces a finite complement clause, indicative or subjunctive. -/
def che : Complementizer where
  morphs := [.free "che"]
  types := .only .declarative

/-- *di* introduces an infinitival complement. -/
def di : Complementizer where
  morphs := [.free "di"]
  coding := some .infinitive

/-- *a* introduces an infinitival complement. -/
def a : Complementizer where
  morphs := [.free "a"]
  coding := some .infinitive

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
some speakers, and a bare infinitive under subject control. -/
def volere : Verb where
  morphs := [.root "volere"]
  valency := .of [(ArgumentFrame.subjunctiveClause, [0, 1]), (ArgumentFrame.infinitival, [0, 1])]
    (controllers := [none, some 0])
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  clauseTypers := [che]

/-- *sperare* 'hope' takes a *che* clause in the subjunctive, the indicative being marginal for
some speakers. -/
def sperare : Verb where
  morphs := [.root "sperare"]
  valency := .ofFrame ArgumentFrame.subjunctiveClause
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)
  clauseTypers := [che]

/-- *intendere* 'intend' takes a bare infinitive under subject control and no finite complement,
in either mood; the periphrasis *avere intenzione di* takes the infinitive with *di*. -/
def intendere : Verb where
  morphs := [.root "intendere"]
  valency := .ofFrame ArgumentFrame.infinitival (controller := some 0)
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- The causative *fare* 'make' takes a bare infinitive under object control, and a finite clause
only as *fare sì che* with the subjunctive, never the indicative. -/
def fare : Verb where
  morphs := [.root "fare"]
  valency := .of
    [(ArgumentFrame.infinitival.withObject, [0, 2, 1]), (ArgumentFrame.subjunctiveClause, [0, 1])]
    (controllers := [some 2])
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

/-! ### Monadic verbs

The monadic verbs of [sorace-2000]'s Italian examples, with the auxiliaries of their perfect,
both for the verbs [maiden-robustelli-2007] §14.20 lists as taking either. -/

/-- *venire* 'come', a verb of change of location. -/
def venire : Verb where
  morphs := [.root "venire"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *arrivare* 'arrive', a verb of change of location. -/
def arrivare : Verb where
  morphs := [.root "arrivare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *cadere* 'fall', a verb of change with a direction ([levin-hovav-1995] p. 147). -/
def cadere : Verb where
  morphs := [.root "cadere"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement
  direction := some .goal

/-- *salire* 'go up', a change along a scale of height. -/
def salire : Verb where
  morphs := [.root "salire"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .accomplishment
  scaleDimension := some .height

/-- *marcire* 'go off, rot', a verb of change of state. -/
def marcire : Verb where
  morphs := [.root "marcire"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .accomplishment

/-- *fiorire* 'bloom', a verb of change of state. -/
def fiorire : Verb where
  morphs := [.root "fiorire"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .achievement

/-- *rimanere* 'remain', the persistence of a state. -/
def rimanere : Verb where
  morphs := [.root "rimanere"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .state
  phasal := some .continuation

/-- *durare* 'last', which takes *essere* for the permanence of a state and *avere* where the
duration is in the foreground. -/
def durare : Verb where
  morphs := [.root "durare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .state

/-- *esistere* 'exist', existence in a state. -/
def esistere : Verb where
  morphs := [.root "esistere"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .state

/-- *bastare* 'be enough', existence in a state. -/
def bastare : Verb where
  morphs := [.root "bastare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .state

/-- *sembrare* 'seem', a state predicated of the subject. -/
def sembrare : Verb where
  morphs := [.root "sembrare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be}
  vendlerClass := some .state

/-- *appartenere* 'belong', which takes *essere* for a state, *L'anello era appartenuto alla regina
Vittoria*, and *avere* where the subject controls it, *Non ho mai appartenuto al PCI*. -/
def appartenere : Verb where
  morphs := [.root "appartenere"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .state

/-- *lavorare* 'work', an activity whose subject controls it. -/
def lavorare : Verb where
  morphs := [.root "lavorare"]
  valency := .ofFrame ArgumentFrame.intransitive [some activitySubjectProfile]
  perfectAuxiliaries := {.have}
  vendlerClass := some .activity

/-- *chiacchierare* 'chat', an activity whose subject controls it. -/
def chiacchierare : Verb where
  morphs := [.root "chiacchierare"]
  valency := .ofFrame ArgumentFrame.intransitive [some activitySubjectProfile]
  perfectAuxiliaries := {.have}
  vendlerClass := some .activity

/-- *correre* 'run', a verb of manner of motion that selects a directional phrase. -/
def correre : Verb where
  morphs := [.root "correre"]
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.spatialPP, [0, 1])]
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .activity
  direction := some .place

/-- *saltare* 'jump', a verb of manner of motion that selects a directional phrase. -/
def saltare : Verb where
  morphs := [.root "saltare"]
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.spatialPP, [0, 1])]
  perfectAuxiliaries := {.be, .have}
  vendlerClass := some .activity
  direction := some .place

/-- *nuotare* 'swim', a verb of manner of motion that selects no directional phrase. -/
def nuotare : Verb where
  morphs := [.root "nuotare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}
  vendlerClass := some .activity
  direction := some .place

/-- *tossire* 'cough', an activity whose subject does not control it. -/
def tossire : Verb where
  morphs := [.root "tossire"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}
  vendlerClass := some .semelfactive

/-- *squillare* 'ring', an activity whose subject does not control it. -/
def squillare : Verb where
  morphs := [.root "squillare"]
  valency := .ofFrame ArgumentFrame.intransitive
  perfectAuxiliaries := {.have}
  vendlerClass := some .activity

/-- `allVerbs` lists the entries. -/
def allVerbs : List Verb :=
  [convincere, pensare, volere, sperare, intendere, fare,
   abbracciare, baciare, coccolare, conoscere, consultare, frequentare, incontrare, incrociare,
   lasciare, sposare, trovare, vedere,
   venire, arrivare, cadere, salire, marcire, fiorire, rimanere, durare, esistere, bastare,
   sembrare, appartenere, lavorare, chiacchierare, correre, saltare, nuotare, tossire, squillare]

/-! ### The perfect auxiliary -/

/-- The auxiliary of the perfect of `v` on the frame `fr` ([maiden-robustelli-2007] §14.20) is
*avere* for a transitive verb; for an intransitive one *essere* when it is a state or expresses a
change, to an endpoint or along a scale, and *avere* when an activity is in the foreground. -/
def perfectAuxiliary (v : Verb) (fr : ArgumentFrame) : PerfectAuxiliary :=
  if fr.HasNominal then .have
  else if v.vendlerClass.any (fun c ↦ c.dynamicity = .stative ∨ c.telicity = .telic) ∨
      v.scaleDimension.isSome then .be
  else .have

theorem perfectAuxiliary_mem : ∀ v ∈ allVerbs, v.perfectAuxiliaries.Nonempty →
    perfectAuxiliary v (v.valency.frames.headD .intransitive) ∈ v.perfectAuxiliaries := by
  decide

/-- *Correre* takes *essere* with a phrase that brings it to an endpoint and *avere* with *verso*
'towards', while *nuotare* keeps *avere* (§14.20). -/
example :
    perfectAuxiliary (correre.withPath Adposition.into) .intransitive = .be ∧
    perfectAuxiliary (correre.withPath { Adposition.into with shape := some .approximative })
      .intransitive = .have ∧
    perfectAuxiliary (nuotare.withPath Adposition.into) .intransitive = .have := by
  decide

end Italian.Verbs
