module

public import Linglib.Syntax.Category.Verb.Basic
public import Linglib.Fragments.Romance.Spanish.Voice

/-!
# Spanish verbs

Spanish verbs of change of state form their intransitive in one of two ways. Most take the
reflexive clitic, as *quebrar* 'crack' does in *el florero se quebró*; a small class takes none,
as *mejorar* 'improve' does in *los sueldos mejoraron*. A few allow both: *hervir* 'boil' is
usually bare and marginally takes the clitic, and the unaccusatives *caer* 'fall' and *morir*
'die' occur with and without it. Each intransitive diathesis records the verb's form in it, with
the clitic where the verb takes it, and whether a verb alternates is read off its diatheses: an
alternating verb has a transitive diathesis and an intransitive one with the patient as
subject. The proto-role entailments of the subject are those
Koontz-Garboden discusses for the causer, and the classification by marking follows Muñoz Pérez.

The verbs with a lexical reciprocal entry beside their transitive use are those of Palmieri's
appendix. They are ordinary verb entries here, and Palmieri's list of them is
`Studies/Palmieri2024.lean`.

The verbs of the dative survey are those whose dative arguments Cuervo classifies, with the
frames the survey uses.

The attitude and causative verbs record the mood of the finite complement each selects in an
affirmative declarative clause, the data of Grano's survey of mood choice and of Portner and
Rubinstein's study of desire verbs; a subjunctive licensed by matrix negation or a question is
not a frame of the verb.

## References

* [A. Koontz-Garboden, *Anticausativization* (2009)][koontz-garboden-2009]
* [G. Palmieri, *Lexical and Grammatical Reciprocity: Perspectives from Romance, Bantu and
  Beyond* (2024)][palmieri-2024]
* [C. Muñoz Pérez, *Stylistic applicatives: A lens into the nature of anticausative SE*
  (2026)][munoz-perez-2026]
* [A. A. Spalek and L. McNally, *The anatomy of a verb* (2026)][spalek-mcnally-2026]
* [T. Grano, *Intention Reports and Eventuality Abstraction in a Theory of Mood Choice*
  (2024)][grano-2024]
* [M. C. Cuervo, *Datives at Large* (2003)][cuervo-2003]
* [portner-rubinstein-2020]
-/

@[expose] public section

namespace Spanish.Verbs

open ArgumentStructure

/-! ### Change-of-state verbs -/

/-- [koontz-garboden-2009]'s EFFECTOR, the subject of a verb whose causer need only cause the
change, whether an agent, an instrument, a natural force or an event. -/
def effectorSubject : EntailmentProfile := {.causation, .independentExistence}

/-- *abrir* 'open', with a marked intransitive *abrirse*. Its causer may be an agent, an
instrument or a natural force ([koontz-garboden-2009]). -/
def abrir : Verb :=
  { morphs := [.root "abrir"],
    valency := .of
      [(ArgumentFrame.np, [0, 1]),
       (ArgumentFrame.intransitive, [1])]
      [some effectorSubject, none] (forms := [none, some [.root "abrir", .encl "se"]]) }

/-- *romper* 'break', with a marked intransitive *romperse*. Its causer may be an agent, an
instrument, a natural force or an event ([koontz-garboden-2009]). -/
def romper : Verb :=
  { morphs := [.root "romper"],
    valency := .of
      [(ArgumentFrame.np, [0, 1]),
       (ArgumentFrame.intransitive, [1])]
      [some effectorSubject, none] (forms := [none, some [.root "romper", .encl "se"]]) }

/-- *hundir* 'sink', with a marked intransitive *hundirse*. Its causer is unrestricted
([koontz-garboden-2009]). -/
def hundir : Verb :=
  { morphs := [.root "hundir"],
    valency := .of
      [(ArgumentFrame.np, [0, 1]),
       (ArgumentFrame.intransitive, [1])]
      [some effectorSubject, none] (forms := [none, some [.root "hundir", .encl "se"]]) }

/-- *caer* 'fall', an unaccusative that occurs with and without the clitic, *cayó* and *se cayó*
([munoz-perez-2026]). -/
def caer : Verb :=
  { morphs := [.root "caer"],
    valency := .ofFrames [ArgumentFrame.intransitive, ArgumentFrame.intransitive]
      (forms := [none, some [.root "caer", .encl "se"]]),
    voiceType := some .nonThematic }

/-- *morir* 'die', an unaccusative that occurs with and without the clitic, *murió* and
*se murió* ([munoz-perez-2026]). -/
def morir : Verb :=
  { morphs := [.root "morir"],
    valency := .ofFrames [ArgumentFrame.intransitive, ArgumentFrame.intransitive]
      (forms := [none, some [.root "morir", .encl "se"]]),
    voiceType := some .nonThematic }

/-- *cerrar* 'close', with a marked intransitive *cerrarse*. -/
def cerrar : Verb :=
  { morphs := [.root "cerrar"],
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
      (forms := [none, some [.root "cerrar", .encl "se"]]) }

/-- *quebrar* 'crack', with a marked intransitive, *el florero se quebró* and never
*el florero quebró* ([munoz-perez-2026]). -/
def quebrar : Verb :=
  { morphs := [.root "quebrar"],
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
      (forms := [none, some [.root "quebrar", .encl "se"]]) }

/-- *hervir* 'boil', whose intransitive is usually bare, *el agua hirvió*, and marginally takes
the clitic ([munoz-perez-2026]). -/
def hervir : Verb :=
  { morphs := [.root "hervir"],
    valency := .of
      [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1]),
        (ArgumentFrame.intransitive, [1])]
      (forms := [none, none, some [.root "hervir", .encl "se"]]) }

/-- *olvidar* 'forget', whose intransitive *olvidarse* takes a dative experiencer,
*se me olvidó*. -/
def olvidar : Verb :=
  { morphs := [.root "olvidar"],
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
      (forms := [none, some [.root "olvidar", .encl "se"]]) }

/-- *ocurrir* 'occur', whose marked form *ocurrirse* takes a dative experiencer,
*se me ocurrió una idea*. -/
def ocurrir : Verb :=
  { morphs := [.root "ocurrir"], valency := .ofFrames [ArgumentFrame.intransitive]
      (forms := [some [.root "ocurrir", .encl "se"]]) }

/-- *mejorar* 'improve', with a bare intransitive, *los sueldos mejoraron* and never
*los sueldos se mejoraron* ([munoz-perez-2026]). -/
def mejorar : Verb :=
  { morphs := [.root "mejorar"],
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])] }

/-- *rasgar* 'tear', with a marked intransitive. Unlike English *tear* it requires a flimsy or
insubstantial patient and a unidirectional, gash-like separation, and it is incompatible with
careful, controlled action ([spalek-mcnally-2026] §3.2). -/
def rasgar : Verb :=
  { morphs := [.root "rasgar"],
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
      (forms := [none, some [.root "rasgar", .encl "se"]]),
    root := { content := {
      force := {.low, .moderate}
      forceDirection := {.unidirectional}
      patientRobustness := {.insubstantial, .flimsy}
      resultGeometry := {.separation, .surfaceBreach}
      agentControl := {.incompatible, .neutral}
    } } }

/-- *asesinar* 'assassinate', whose causer must be an agent, has no intransitive, since with
the clitic it is only reflexive, *el senador se asesinó* 'the senator killed himself'
([koontz-garboden-2009] exx. 24–29). -/
def asesinar : Verb :=
  { morphs := [.root "asesinar"],
    valency := .ofFrame ArgumentFrame.np [some accomplishmentSubjectProfile, none] }

/-- *cortar* 'cut', which requires an agent and has no intransitive in that sense
([koontz-garboden-2009]). In the sense 'snap' it has the marked intransitive of
*se me cortó la correa* 'the strap snapped on me' ([munoz-perez-2026]), which the marking
records; the frames are those of 'cut'. -/
def cortar : Verb :=
  { morphs := [.root "cortar"],
    valency := .ofFrame ArgumentFrame.np [some accomplishmentSubjectProfile, none] }

/-- *cortar* in the sense 'snap', with the marked intransitive of *se me cortó la correa* 'the
strap snapped on me' ([munoz-perez-2026]). -/
def cortarInchoative : Verb :=
  { morphs := [.root "cortar"], senseTag := .inchoative,
    valency := .ofFrames [ArgumentFrame.intransitive]
      (forms := [some [.root "cortar", .encl "se"]]) }

/-- *ahogar* 'drown', with an EFFECTOR causer and typically an animate theme; *ahogarse* is its
derived inchoative ([koontz-garboden-2009] exx. 50–52). -/
def ahogar : Verb :=
  { morphs := [.root "ahogar"],
    valency := .of
      [(ArgumentFrame.np, [0, 1]),
       (ArgumentFrame.intransitive, [1])]
      [some effectorSubject, none] (forms := [none, some [.root "ahogar", .encl "se"]]) }

/-- *empeorar* 'worsen', an internally caused change of state with a bare intransitive, which
rejects *por sí solo* 'by itself' ([koontz-garboden-2009] ex. 65a). -/
def empeorar : Verb :=
  { morphs := [.root "empeorar"],
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])] }

/-- *quemar* 'burn', with a marked intransitive *quemarse*. -/
def quemar : Verb :=
  { morphs := [.root "quemar"],
    valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
      (forms := [none, some [.root "quemar", .encl "se"]]) }

/-- *crecer* 'grow', an internally caused change of state, which rejects *por sí solo* 'by
itself' ([koontz-garboden-2009] ex. 65c). -/
def crecer : Verb :=
  { morphs := [.root "crecer"], valency := .ofFrame ArgumentFrame.intransitive }

/-- The verbs of the fragment. -/
def allVerbs : List Verb :=
  [abrir, romper, hundir, caer, morir, cerrar, quebrar, hervir, olvidar, ocurrir, mejorar, rasgar,
    asesinar, cortar, cortarInchoative, ahogar, empeorar, crecer, quemar]

theorem romper_marks_anticausative : romper.Marks anticausative := by decide

theorem mejorar_alternates_not_marks :
    mejorar.Alternates Voice.anticausative ∧ ¬ mejorar.Marks anticausative := by
  decide

/-! ### Verbs of the dative survey

The verbs whose dative arguments [cuervo-2003] surveys, by the frames they show there:
transitive activities, unaccusatives of movement, happening and existence, a dative-experiencer
psych verb and two unergatives, one of which also takes an object. -/

/-- *mandar* 'send' — transitive, directional towards a recipient. -/
def mandar : Verb where
  morphs := [.root "mandar"]
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.np_pp]

/-- *preparar* 'fix, prepare' — transitive verb of creation. -/
def preparar : Verb where
  morphs := [.root "preparar"]
  valency := .ofFrame ArgumentFrame.np

/-- *sacar* 'take away' — transitive, directional away from a source. -/
def sacar : Verb where
  morphs := [.root "sacar"]
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.np_pp]

/-- *lavar* 'wash' — transitive activity, non-directional. -/
def lavar : Verb where
  morphs := [.root "lavar"]
  valency := .ofFrame ArgumentFrame.np

/-- *admirar* 'admire' — transitive stative. -/
def admirar : Verb where
  morphs := [.root "admirar"]
  valency := .ofFrame ArgumentFrame.np

/-- *llegar* 'arrive' — unaccusative verb of movement. -/
def llegar : Verb where
  morphs := [.root "llegar"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic

/-- *salir* 'come out' — unaccusative verb of movement. -/
def salir : Verb where
  morphs := [.root "salir"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic

/-- *suceder* 'happen' — unaccusative verb of happening. -/
def suceder : Verb where
  morphs := [.root "suceder"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic

/-- *sobrar* 'be left over, be extra' — unaccusative existential. -/
def sobrar : Verb where
  morphs := [.root "sobrar"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic

/-- *gustar* 'appeal to, be liked by' — unaccusative psych verb whose experiencer is dative. -/
def gustar : Verb where
  morphs := [.root "gustar"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic

/-- *caminar* 'walk' — unergative. -/
def caminar : Verb where
  morphs := [.root "caminar"]
  valency := .ofFrame ArgumentFrame.intransitive

/-- *correr* 'run' — unergative, also transitive with an object naming the race run. -/
def correr : Verb where
  morphs := [.root "correr"]
  valency := .ofFrames [ArgumentFrame.intransitive, ArgumentFrame.np]

/-! ### Verbs with a lexical reciprocal entry -/

/-- *abrazar* 'hug' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def abrazar : Verb where
  morphs := [.root "abrazar"]
  valency := .ofFrame ArgumentFrame.np

/-- *acurrucar* 'cuddle' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def acurrucar : Verb where
  morphs := [.root "acurrucar"]
  valency := .ofFrame ArgumentFrame.np

/-- *besar* 'kiss' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def besar : Verb where
  morphs := [.root "besar"]
  valency := .ofFrame ArgumentFrame.np

/-- *casar* 'marry' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def casar : Verb where
  morphs := [.root "casar"]
  valency := .ofFrame ArgumentFrame.np

/-- *consultar* 'consult/confer' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def consultar : Verb where
  morphs := [.root "consultar"]
  valency := .ofFrame ArgumentFrame.np

/-- *cruzar* 'run into, meet accidentally' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def cruzar : Verb where
  morphs := [.root "cruzar"]
  valency := .ofFrame ArgumentFrame.np

/-- *dejar* 'leave/break up' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def dejar : Verb where
  morphs := [.root "dejar"]
  valency := .ofFrame ArgumentFrame.np

/-- *encontrar* 'find/meet' — transitive, with a lexical reciprocal entry
    ([palmieri-2024], Appendix A). -/
def encontrar : Verb where
  morphs := [.root "encontrar"]
  valency := .ofFrame ArgumentFrame.np

/-! ### Attitude and causative verbs -/

/-- *creer* 'believe' takes a *que* clause in the indicative. -/
def creer : Verb where
  morphs := [.root "creer"]
  valency := .ofFrames [ArgumentFrame.finiteClause]
  opaqueContext := true
  attitude := some (.doxastic .nonVeridical)

/-- *querer* 'want' takes a *que* clause in the subjunctive, with disjoint reference, and an
infinitive under subject control. -/
def querer : Verb where
  morphs := [.root "querer"]
  valency := .ofFrames [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
    (controllers := [none, some 0])
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- *esperar* 'hope' takes a *que* clause in the subjunctive and an infinitive under subject
control. With an indicative clause about the future the verb means 'expect', a sense this entry
does not cover. -/
def esperar : Verb where
  morphs := [.root "esperar"]
  valency := .ofFrames [ArgumentFrame.subjunctiveClause, ArgumentFrame.infinitival]
    (controllers := [none, some 0])
  passivizable := false
  opaqueContext := true
  attitude := some (.preferential .positive true)

/-- The causative *hacer* 'make' takes an infinitive under object control and a *que* clause in
the subjunctive. -/
def hacer : Verb where
  morphs := [.root "hacer"]
  valency := .of
    [(ArgumentFrame.infinitival.withObject, [0, 2, 1]), (ArgumentFrame.subjunctiveClause, [0, 1])]
    (controllers := [some 2])

/-- *convencer* 'convince' takes an object and a *de que* clause, which reports an intention in
the subjunctive and a belief in the indicative. -/
def convencer : Verb where
  morphs := [.root "convencer"]
  valency := .ofFrames
    [⟨some .nominal, [.nominal, .clausal (some .subjunctive) (.only .declarative)]⟩,
     ⟨some .nominal, [.nominal, .clausal (some .indicative) (.only .declarative)]⟩]
  opaqueContext := true

end Spanish.Verbs
