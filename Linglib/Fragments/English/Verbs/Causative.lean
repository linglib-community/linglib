module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English causative verbs

The English periphrastic causatives are *cause*, *make*, *let*, *have*, *get*, *force* and
*prevent*, and the lexical causatives here are *kill*, *break* and *tear*. Karttunen counts
*cause*, *make*, *have* and *force* among the verbs whose affirmation implies the complement, and
*prevent* among those whose affirmation implies its negation.

## References

* [karttunen-1971]
* [levin-1993]
* [majid-boster-bowerman-2008]
* [spalek-mcnally-2026]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree

/-! ### Causative (Periphrastic) -/

/-- *cause* takes an object and an infinitive, *cause the vase to fall*. -/
def cause : Verb where
  morphs := [.root "cause"]
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)
  vendlerClass := some .accomplishment
  implicative := ⟨.some .positive, ⊥⟩
  levinClasses := {LevinClass.engender}

/-- *make* takes an object and a bare infinitive, *make him leave*. Levin does not class it (the
*make* of 26.1 is the verb of creation and that of 29.3 the dub verb). -/
def make : Verb where
  morphs := [.root "make"]
  past := "made"
  valency := .ofFrame ArgumentFrame.smallClause.withObject (controller := some 1)
  vendlerClass := some .accomplishment
  implicative := ⟨.some .positive, ⊥⟩
  levinExcluded := {LevinClass.build, .dub}

/-- *let* is the permissive causative, *let him leave*. -/
def let_ : Verb where
  morphs := [.root "let"]
  past := "let"
  valency := .ofFrame ArgumentFrame.smallClause.withObject (controller := some 1)
  vendlerClass := some .achievement

/-- *have* in its causative use takes an object and a bare infinitive, *have him leave*. -/
def have_caus : Verb where
  morphs := [.root "have"]
  thirdSg := "has"
  past := "had"
  valency := .ofFrame ArgumentFrame.smallClause.withObject (controller := some 1)
  vendlerClass := some .achievement
  implicative := ⟨.some .positive, ⊥⟩
  senseTag := .causative

/-- *get* in its causative use takes an object and an infinitive, *get him to leave*. Levin does
not class it (the *get* of 13.5.1 is the verb of obtaining). -/
def get_caus : Verb where
  morphs := [.root "get"]
  past := "got"
  pastPart := "gotten"
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)
  vendlerClass := some .accomplishment
  senseTag := .causative
  levinExcluded := {LevinClass.get}

/-- *force* takes an object and an infinitive, *force him to leave*. -/
def force : Verb where
  morphs := [.root "force"]
  valency := .ofFrame ArgumentFrame.infinitival.withObject (controller := some 1)
  vendlerClass := some .accomplishment
  implicative := ⟨.some .positive, ⊥⟩

/-- *prevent* takes an object and a *from*-gerund, *prevent him from leaving*. -/
def prevent : Verb where
  morphs := [.root "prevent"]
  valency := .ofFrame ArgumentFrame.gerund.withObject (controller := some 1)
  vendlerClass := some .accomplishment
  implicative := ⟨.some .negative, ⊥⟩

/-! ### Lexical Causatives -/

/-- "kill" — Levin 42.1 murder verbs. -/
def kill : Verb where
  morphs := [.root "kill"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  root := { content := {
    resultGeometry := {.totalDestruction}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.murder}

/-- "break" — Levin 45.1 break verbs, a change in "material integrity" with no specification
    of how the change comes about ([levin-1993]:241). -/
def break_ : Verb where
  morphs := [.root "break"]
  past := "broke"
  pastPart := "broken"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 2])]
  vendlerClass := some .accomplishment
  root := { content := {
    force := {.moderate, .high}
    -- direction unconstrained: *break* covers snapping (bidirectional),
    -- hammering (omnidirectional), and directed blows (unidirectional)
    patientRobustness := {.moderate, .robust}
    -- English speakers describe both snapping and smashing with *break*
    -- ([majid-boster-bowerman-2008])
    resultGeometry := {.fracture, .fragmentation}
    agentControl := {.incompatible, .neutral}
  } }
  levinClasses := {LevinClass.appear, .break_, .cheat, .hurt, .split}

/-- *tear* is a break verb (Levin's 45.1) of separation in contrary directions with force. Unlike
    *break*, it implies a direction, bidirectional or pulling apart, is compatible with careful
    controlled action, and takes as patient any solid capable of irregular separation
    ([spalek-mcnally-2026] §3.1–3.2). In [majid-boster-bowerman-2008] ten of twenty-eight
    languages have a verb used only for tearing cloth by hand, and English speakers extend
    *tear* to pulling yarn apart. -/
def tear_ : Verb where
  morphs := [.root "tear"]
  past := "tore"
  pastPart := "torn"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 1, 2])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    force := {.moderate, .high}
    forceDirection := {.bidirectional, .unidirectional}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.separation}
    agentControl := {.neutral, .compatible}
    instrument := {.hands}
  } }
  levinClasses := {LevinClass.break_, .run, .split}

end English.Verbs
