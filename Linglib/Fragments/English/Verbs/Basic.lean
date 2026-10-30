module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Syntax.Voice.Basic
public import Linglib.Semantics.ArgumentStructure.LevinClass.Members
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Morphology.Word.Basic
public import Linglib.Fragments.English.Inflection
public import Linglib.Fragments.English.Adpositions

/-!
# English verbs

This file defines the English verb entry and the simplest verbs. An entry extends the
cross-linguistic `Verb`, with its argument frames, aspectual and semantic class, presupposition,
causation and attitude facets, by the forms a dictionary lists, the past and past participle of
an irregular verb. `Verb.inflect` gives the morphs of each cell, the base with the regular suffix
on its root where no form is listed, and `Verb.realize` their spelling by the rules of
`English.Inflection`. The verbs here are the plain intransitives, transitives and ditransitives
that the studies reach for first, *sleep*, *kick*, *give* and the like, and a few verbs of
consumption and creation; the other classes are in the sibling files and `Verbs/Inventory.lean`
lists them all. A citation form with several entries is a polysemous lexeme told apart by
`senseTag`. An entry's `levinClasses` are the classes whose member lists in Levin's book carry
its citation form, less the classes that list the form in a sense the entry is not, and
`scripts/check_levin_classes.py` checks the entries against the lists.

## References

* [levin-1993]
* [bruening-2021]
* [fillmore-1986]
* [levin-hovav-1995]
* [huddleston-pullum-2002]
-/

@[expose] public section

open Morphology

namespace English.Verbs

open ArgumentStructure Aspect Degree

/-! ### The entry type -/

/-- An English verb is the cross-linguistic `Verb` with the forms that the regular suffixes do not
give. An entry that lists none is regular. -/
structure Verb extends _root_.Verb where
  /-- The third person singular present, where it is not the *-s* form, as in *has*. -/
  thirdSg : Option String := none
  /-- The past, where it is not the *-ed* form, as in *ran*. -/
  past : Option String := none
  /-- The past participle, where it is not the past, as in *run* and *shown*. -/
  pastPart : Option String := none
  /-- A base of more than one syllable doubles its final consonant letter before *-ed* and
  *-ing*, as one stressed on its last syllable does, *regretted* against *visited*. -/
  doubling : Bool := false
  deriving BEq

/-- The inflectional cells of an entry. -/
inductive Verb.Cell where
  | base
  | thirdSg
  /-- The plain present, of every subject but the third person singular
  ([huddleston-pullum-2002] ch. 3 §1.1). -/
  | plainPresent
  | past
  | pastParticiple
  | presentParticiple
  deriving DecidableEq, Repr, Fintype

/-- `v.onRoot listed suffix` is the entry's morphs with the root replaced by the listed form,
or with the suffix on the root where no form is listed. -/
def Verb.onRoot (v : Verb) (listed : Option String) (suffix : Morph) : List Morph :=
  v.morphs.flatMap fun m ↦
    if m.kind = .root then listed.elim [m, suffix] fun f ↦ [.root f] else [m]

/-- The morphs of an entry in each cell. The past participle is the past unless the entry lists
one, and no entry lists a present participle. -/
def Verb.inflect (v : Verb) : Verb.Cell → List Morph
  | .base | .plainPresent => v.morphs
  | .thirdSg => v.onRoot v.thirdSg Inflection.s
  | .past => v.onRoot v.past Inflection.ed
  | .pastParticiple => v.onRoot (v.pastPart <|> v.past) Inflection.ed
  | .presentParticiple => v.onRoot none Inflection.ing

/-- The form an entry realizes in each cell, the spelling of its morphs there. -/
def Verb.realize (v : Verb) (c : Verb.Cell) : String := Inflection.spell (v.inflect c) v.doubling

@[simp] theorem Verb.realize_plainPresent (v : Verb) :
    v.realize .plainPresent = v.realize .base := rfl

theorem Verb.realize_pastParticiple {v : Verb} (h : v.pastPart = none) :
    v.realize .pastParticiple = v.realize .past := by
  simp [realize, inflect, h]

/-! ### Simple -/

/-- "sleep" — intransitive, no presupposition -/
def sleep : Verb where
  morphs := [.root "sleep"]
  past := "slept"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.fit, .snooze}

/-- "sneeze" — intransitive -/
def sneeze : Verb where
  morphs := [.root "sneeze"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  levinClasses := {LevinClass.hiccup, .nonverbalExpression}

/-- *run*, an agentive verb of manner of motion, whose causative takes a directional phrase, *We
ran the mouse through the maze* but not *We ran the mouse* ([levin-hovav-1995] p. 111). -/
def run : Verb where
  morphs := [.root "run"]
  past := "ran"
  pastPart := "run"
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np_spatialPP, [1, 0, 2]),
     (ArgumentFrame.spatialPP, [0, 2])]
    [some activitySubjectProfile, none, none]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place
  root := { content := {
    force := {.moderate}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.meander, .prepare, .run, .swarm}

/-- "dance" — intransitive activity -/
def dance : Verb where
  morphs := [.root "dance"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.modeOfBeingInvolvingMotion, .performance, .waltz}

/-- "arrive" — unaccusative intransitive -/
def arrive : Verb where
  morphs := [.root "arrive"]
  valency := .ofFrame ArgumentFrame.intransitive [some achievementSubjectProfile]
  voiceType := some .nonThematic
  passivizable := false
  vendlerClass := some .achievement
  direction := some .goal
  levinClasses := {LevinClass.inherentlyDirectedMotion}

/-- *come*, an unaccusative verb of inherently directed motion like *arrive* (51.1). -/
def come : Verb where
  morphs := [.root "come"]
  past := "came"
  pastPart := "come"
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic
  passivizable := false
  vendlerClass := some .achievement
  direction := some .goal
  levinClasses := {LevinClass.appear, .inherentlyDirectedMotion}

/-- "go" — Levin 51.1 inherently directed motion, suppletive in the past. -/
def go : Verb where
  morphs := [.root "go"]
  past := "went"
  pastPart := "gone"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.inherentlyDirectedMotion}
  levinExcluded := {LevinClass.meander}

/-- In *run into the room* the spatial value *into* marks, the illative, makes a verb of manner of
motion directed and telic, while *run behind the house* leaves it as it is, and so does any path
phrase *sleep*, which selects none. -/
example : (∀ c ∈ Adpositions.into.functions, c.kind = .spatial →
      (run.withPath (.ofCase c)).direction = some .goal ∧
        (run.withPath (.ofCase c)).vendlerClass = some .accomplishment) ∧
    run.withPath Adposition.behind = run.toVerb ∧ sleep.withPath (.ofCase .ill) = sleep.toVerb :=
  ⟨by decide, rfl, rfl⟩

/-- *Dance* says nothing of a path, *run* displaces its subject without a direction, and *arrive*
lexicalizes a goal ([levin-hovav-1995] p. 147). -/
example : dance.direction = none ∧ run.direction = some .place ∧ arrive.direction = some .goal :=
  ⟨rfl, rfl, rfl⟩

/-- "eat" — transitive, implicit object is indefinite ("Have you eaten?") -/
def eat : Verb where
  morphs := [.root "eat"]
  past := "ate"
  pastPart := "eaten"
  valency := .ofFrames
    [ArgumentFrame.np,
     ArgumentFrame.objectDrop (some .indef),
     ArgumentFrame.pp (some Adpositions.at_)]
    [some accomplishmentSubjectProfile, some consumptionObject]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    force := {.low, .moderate}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.eat}

/-- "kick" — transitive -/
def kick : Verb where
  morphs := [.root "kick"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
    [some accomplishmentSubjectProfile, some contactObject, none, none]
  vendlerClass := some .activity
  root := { content := {
    force := {.moderate, .high}
    forceDirection := {.unidirectional}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.bodyInternalMotion, .carry, .crane, .hit, .split, .throw}

/-- The conative *at* of *eat at* marks no value, so *eat* selects no spatial phrase, while the
*on* of *kick him on the shin* locates the contact on a surface. -/
example : ¬ eat.TakesSpatial ∧ kick.TakesSpatial := by decide

/-- "aim" — with an *at*-phrase, and transitive with one -/
def aim : Verb where
  morphs := [.root "aim"]
  valency := .of
    [(ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.at_), [0, 2, 1])]

/-- "give" — ditransitive, alternates DOC/PP. The direct object may be implicit in the
    prepositional frame only, an indefinite (*She gives to the Red Cross*); the PP may be
    implicit, a definite ([fillmore-1986]: pragmatically recoverable). -/
def give : Verb where
  morphs := [.root "give"]
  past := "gave"
  pastPart := "given"
  valency := .of
    [(ArgumentFrame.np_np, [0, 1, 2]),
     (ArgumentFrame.np_pp, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 2, 1]),
     ((ArgumentFrame.np_pp (some Adpositions.to_) (some .dat)).leaveImplicit 0 (some .indef),
       [0, 2, 1]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .def), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "put" — locative -/
def put : Verb where
  morphs := [.root "put"]
  past := "put"
  valency := .ofFrame ArgumentFrame.np_pp
  vendlerClass := some .achievement
  levinClasses := {LevinClass.put}

/-- "weigh" — measure predicate selecting for mass/weight. -/
def weigh : Verb where
  morphs := [.root "weigh"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.register}

/-- "cover" — motion/extent predicate selecting for distance. -/
def cover : Verb where
  morphs := [.root "cover"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.contiguousLocation, .fill}

/-- "measure" — general measurement predicate. -/
def measure : Verb where
  morphs := [.root "measure"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.register}

/-- "buy" — irregular transitive -/
def buy : Verb where
  morphs := [.root "buy"]
  past := "bought"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_) (some .ben), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
    [some possessionTransfer.subjectProfile, none, none]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.get}

/-- "meet" — irregular transitive -/
def meet : Verb where
  morphs := [.root "meet"]
  past := "met"
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.objectDrop (some .reciprocal)]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.contiguousLocation, .meet}

/-- "set" — irregular; the base, past and past participle forms coincide. -/
def set_ : Verb where
  morphs := [.root "set"]
  past := "set"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement
  levinClasses := {LevinClass.braid, .imageImpression, .prepare, .put}

/-- "clarify" — regular transitive. -/
def clarify : Verb where
  morphs := [.root "clarify"]
  valency := .ofFrame ArgumentFrame.np

/-- "sell" — change of possession, alternates DOC/PP.
    Implicit DO is definite; implicit goal is indefinite. -/
def sell : Verb where
  morphs := [.root "sell"]
  past := "sold"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     ((ArgumentFrame.np_pp (some Adpositions.to_) (some .dat)).leaveImplicit 0 (some .def),
       [0, 1, 2]),
     ((ArgumentFrame.np_pp).leaveImplicit 1 (some .indef), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1])]
    [some possessionTransfer.subjectProfile, none, none]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.give}

/-- "leave" — transitive (also used intransitively with argument drop) -/
def leave : Verb where
  morphs := [.root "leave"]
  past := "left"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement
  levinClasses := {LevinClass.fulfilling, .futureHaving, .get, .inherentlyDirectedMotion, .keep,
    .leave}

/-- "see" — transitive; factive with a finite-clause complement -/
def see : Verb where
  morphs := [.root "see"]
  past := "saw"
  pastPart := "seen"
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.finiteClause]
    [some perception.subjectProfile, none]
  vendlerClass := some .state
  attitude := some (.doxastic .epistemic)
  factivity := some .semi
  levinClasses := {LevinClass.characterize, .see}

/-! ### Other -/

/-- "devour" — transitive, no presupposition -/
def devour : Verb where
  morphs := [.root "devour"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    force := {.moderate, .high}
    agentControl := {.neutral}
  } }
  levinClasses := {LevinClass.devour}

/-- "drink" — Levin 39.1 Eat verbs. -/
def drink : Verb where
  morphs := [.root "drink"]
  past := "drank"
  pastPart := "drunk"
  valency := .ofFrames
    [ArgumentFrame.np,
     ArgumentFrame.objectDrop (some .indef),
     ArgumentFrame.pp (some Adpositions.at_)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.eat}

/-- "read" — Levin 14 Learn verbs, with learn and study; also listed among the verbs of
    transfer of a message (37.1) and the register verbs (54.1). -/
def read : Verb where
  morphs := [.root "read"]
  past := "read"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .incremental
  levinClasses := {LevinClass.learn, .register, .transferOfMessage}

/-- "build" — creation verb, strictly incremental theme.
    Base transitive that productively takes DOC ("build us a house"). -/
def build : Verb where
  morphs := [.root "build"]
  past := "built"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_) (some .ben), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.out), [0, 1, 3]),
     (ArgumentFrame.np_pp (some Adpositions.into) (some .transl), [0, 3, 1])]
    [some accomplishmentSubjectProfile, some creationObject, none, none]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.build}

/-- "write" — Levin 25.2 Scribble verbs, cross-listed with the build verbs;
    creation verb, strictly incremental theme.
    Alternates DOC/PP, and uniquely allows an implicit direct object, an indefinite, in both
    (*She wrote me*, *She wrote to me*; [bruening-2021]). -/
def write : Verb where
  morphs := [.root "write"]
  past := "wrote"
  pastPart := "written"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp, [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .indef), [0, 2, 1]),
     ((ArgumentFrame.np_pp).leaveImplicit 0 (some .indef), [0, 1, 2]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.performance, .scribble, .transferOfMessage}

/-- "do", the lexical verb of *She does her best*, a lexeme apart from the auxiliary *do*
([huddleston-pullum-2002] ch. 3 §2). -/
def do_ : Verb where
  morphs := [.root "do"]
  past := "did"
  pastPart := "done"
  valency := .ofFrame ArgumentFrame.np

/-- "sweep" — motion + sustained contact, variable agentivity (default sense). -/
def sweep : Verb where
  morphs := [.root "sweep"]
  past := "swept"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_spatialPP, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
    [some wipeManner.subjectProfile, none, none]
  vendlerClass := some .activity
  passivizable := true
  root := { content := {
    force := {.low, .moderate}
    forceDirection := {.unidirectional}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.entitySpecificModeOfBeing, .funnel, .meander, .run, .wipeManner}

/-- "sweep" instrument sense — obligatorily agentive, broom lexicalized. -/
def sweep_instr : Verb where
  morphs := [.root "sweep"]
  past := "swept"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_spatialPP, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
    [some wipeInstrument.subjectProfile, none, none]
  vendlerClass := some .activity
  passivizable := true
  senseTag := .instrumental
  root := { content := {
    force := {.low, .moderate}
    forceDirection := {.unidirectional}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.entitySpecificModeOfBeing, .funnel, .meander, .run, .wipeManner}

/-! ### Words -/

/-- The morphosyntactic features of an inflectional cell. -/
def Verb.Cell.features : Verb.Cell → Features
  | .base => Features.of (verbForm := some .Inf)
  | .thirdSg => Features.of (number := some .singular) (person := some .third)
      (voice := some .Act) (verbForm := some .Fin) (tense := some .Pres)
  | .plainPresent => Features.of (voice := some .Act) (verbForm := some .Fin) (tense := some .Pres)
  | .past => Features.of (verbForm := some .Fin) (voice := some .Act) (tense := some .Past)
  | .pastParticiple => Features.of (verbForm := some .Part)
  | .presentParticiple => Features.of (verbForm := some .Part)

/-- The entry's form in a cell as a `Word`, with the cell's features. -/
def Verb.toWord (v : Verb) (c : Verb.Cell) : Word :=
  { form := v.realize c, cat := .VERB, features := c.features }

/-- The past participle in passive voice, the same form as `toWord .pastParticiple` marked
passive. -/
def Verb.passiveParticiple (v : Verb) : Word :=
  { form := v.realize .pastParticiple, cat := .VERB,
    features := Features.of (verbForm := some .Part) (voice := some .Pass) }

end English.Verbs
