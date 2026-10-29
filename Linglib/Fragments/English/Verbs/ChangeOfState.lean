module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English change-of-state verbs

This file defines the English change-of-state verbs: the physical disturbance verbs of Tham's
study, the further change-of-state verbs of Martin, Rose and Nichols's, Levin's class of
*freeze*, *heat*, *bend*, *boil*, *rust* and *increase*, and the degree achievement pairs of
Kennedy's, *straighten*, *flatten*, *open*, *lengthen*, *widen*, *cool* and *warm*, each with
the frames of its causative and anticausative uses.

## References

* [kennedy-2007]
* [rappaport-hovav-2014]
* [tham-2025]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree

/-! ### Physical disturbance change-of-state verbs ([tham-2025]) -/

/-- "crack" — Levin 45.1 Break verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale (contra [rappaport-hovav-2014] two-point
    classification), but allows BOTH telic ("cracked in a minute") and atelic
    ("cracked for two days") readings. Compatible with *completely*, *partially*,
    *badly*. The verb is NOT a standard degree achievement: its variable telicity
    does not reduce to scale boundedness alone. -/
def crack : Verb where
  morphs := [.root "crack"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .achievement
  scaleDimension := some .cracking
  levinClasses := {LevinClass.break_, .soundEmission}

/-- "dent" — Levin 21.2 Carve verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale, compatible with *more dented*, *completely
    dented*, *badly dented*. -/
def dent : Verb where
  morphs := [.root "dent"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .achievement
  scaleDimension := some .denting
  levinClasses := {LevinClass.carve}

/-- "scratch" — Levin 21.1 Cut verbs, a physical disturbance CoS verb for
    [tham-2025]: closed scale, compatible with *more scratched*, *completely
    scratched*, *badly scratched*. Levin also lists it among the wipe verbs
    (§10.4.1) and the swat verbs (§18.2) on its manner readings. -/
def scratch : Verb where
  morphs := [.root "scratch"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .achievement
  scaleDimension := some .scratching
  levinClasses := {LevinClass.cut, .hurt, .rummage, .scribble, .swat, .wipeManner}

/-- "shatter" — Levin 45.1 Break verbs. NOT a physical disturbance verb.
    Punctual, non-gradable: *shatter in two minutes* (after, not duration),
    #*shatter for two minutes*, ??*more shattered* ([tham-2025] (12)). -/
def shatter : Verb where
  morphs := [.root "shatter"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.break_}

/-- "burn" — destruction or transformation by fire or heat; Levin 45.4 other change-of-state
    verbs. -/
def burn : Verb where
  morphs := [.root "burn"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    force := {.moderate, .high}
    patientRobustness := {.flimsy, .moderate, .robust}
    resultGeometry := {.totalDestruction, .deformation}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.entitySpecificChangeOfState, .entitySpecificModeOfBeing, .hurt,
    .lightEmission, .otherChangeOfState, .tingle}

/-- "destroy" — Levin 44 destroy verbs. -/
def destroy : Verb where
  morphs := [.root "destroy"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  root := { content := {
    resultGeometry := {.totalDestruction}
    agentControl := {.neutral, .compatible}
  } }
  levinClasses := {LevinClass.destroy}

/-- "melt" — change of consistency by heat; Levin 45.4 other change-of-state verbs. A base
    transitive that takes a double-object benefactive ("melt me some ice cream") and an
    indefinite implicit object ("the ice cream melted" / "we're melting"). -/
def melt : Verb where
  morphs := [.root "melt"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 3, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    force := {.low, .moderate}
    patientRobustness := {.moderate, .robust}
    resultGeometry := {.deformation}
    agentControl := {.compatible}
  } }
  levinClasses := {LevinClass.knead, .otherChangeOfState}

/-! ### Further change-of-state verbs

The causative verbs Martin, Rose and Nichols survey that have no entry elsewhere in this
file. -/

/-- "activate" — sets a device or process in operation; not listed by Levin. -/
def activate : Verb where
  morphs := [.root "activate"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment


/-- "affect" — Levin 31.1 amuse verbs. -/
def affect : Verb where
  morphs := [.root "affect"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  levinClasses := {LevinClass.amuse}

/-- "change" — transformation; Levin 26.6 turn verbs. -/
def change : Verb where
  morphs := [.root "change"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.into) (some .transl), [0, 1, 2]),
     (⟨some .nominal, [.nominal, .adposition (some Adpositions.from_),
     .adposition (some Adpositions.into) (some .transl)]⟩, [0, 1, 3, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.dress, .exchange, .otherChangeOfState, .turn}

/-- "damage" — partial destruction; not listed by Levin. -/
def damage : Verb where
  morphs := [.root "damage"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment


/-- "eliminate" — removal; Levin 42.1 murder verbs. -/
def eliminate : Verb where
  morphs := [.root "eliminate"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.murder, .remove}

/-- "hurt" — Levin 40.8.3 hurt verbs. -/
def hurt : Verb where
  morphs := [.root "hurt"]
  past := "hurt"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.amuse, .hurt, .marvel, .pain}

/-- "restore" — Levin 13.2 contribute verbs. -/
def restore : Verb where
  morphs := [.root "restore"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute}

/-- "trigger" — sets a process off; not listed by Levin. -/
def trigger : Verb where
  morphs := [.root "trigger"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement

/-- "bury" — covering with earth. Levin's concealment class (§16) does not list *bury*. -/
def bury : Verb where
  morphs := [.root "bury"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment


/-- "drop" — Levin 45.6 calibratable change-of-state verbs. -/
def drop : Verb where
  morphs := [.root "drop"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.calibratableChangeOfState, .meander, .putDirection, .roll}

/-- "lift" — Levin 9.4 verbs of putting with a specified direction. -/
def lift : Verb where
  morphs := [.root "lift"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.putDirection, .steal}

/-- "lock" — securing with a lock; Levin lists *lock* only among the tape verbs (§22.4). -/
def lock : Verb where
  morphs := [.root "lock"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.tape}


/-- "shut" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def shut : Verb where
  morphs := [.root "shut"]
  past := "shut"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.otherChangeOfState}

/-- "spread" — Levin 9.7 spray/load verbs. -/
def spread : Verb where
  morphs := [.root "spread"]
  past := "spread"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 2]),
     (ArgumentFrame.np_spatialPP, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.appear, .entitySpecificModeOfBeing, .sprayLoad}

/-- "stretch" — Levin 45.4 other change-of-state verbs. -/
def stretch : Verb where
  morphs := [.root "stretch"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.crane, .meander, .otherChangeOfState}

/-- "switch" — Levin's change-of-state lists do not include *switch*. -/
def switch : Verb where
  morphs := [.root "switch"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment


/-- "close" — Levin 45.4 other change-of-state verbs, zero-related to the adjective, and
    40.3.2 crane verbs (*close one's eyes*). -/
def close : Verb where
  morphs := [.root "close"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.crane, .otherChangeOfState}

/-- "dry" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def dry : Verb where
  morphs := [.root "dry"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  scaleDimension := some .wetness
  scalePolarity := .negative
  levinClasses := {LevinClass.otherChangeOfState}

/-- "enhance" — improvement in quality; not listed by Levin. -/
def enhance : Verb where
  morphs := [.root "enhance"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "extend" — Levin 47.1 exist verbs, 13.2 contribute verbs and 13.3 verbs of future
    having. -/
def extend : Verb where
  morphs := [.root "extend"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute, .exist, .futureHaving}

/-- "lower" — Levin 9.4 verbs of putting with a specified direction. -/
def lower : Verb where
  morphs := [.root "lower"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.putDirection}

/-- "slow" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def slow : Verb where
  morphs := [.root "slow"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .activity
  scaleDimension := some .speed
  levinClasses := {LevinClass.otherChangeOfState}

/-- "turn" — Levin 26.6 turn verbs (*turn the prince into a frog*). -/
def turn : Verb where
  morphs := [.root "turn"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.into) (some .transl), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.turn}
  levinExcluded := {LevinClass.crane, .hurt, .meander, .roll}

/-- "wake up" — the particle verb of awakening; Levin lists *waken* but not *wake*. -/
def wakeUp : Verb where
  morphs := [.root "wake", .free "up"]
  past := "woke"
  pastPart := "woken"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .achievement

/-! ### Change of State (§ 45) -/

/-- "freeze" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def freeze : Verb where
  morphs := [.root "freeze"]
  past := "froze"
  pastPart := "frozen"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.knead, .otherChangeOfState, .weather}

/-- "heat" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def heat : Verb where
  morphs := [.root "heat"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.cooking, .otherChangeOfState}

/-- "bend" — Levin 45.2 Bend verbs. Causative/inchoative alternation.
    Degree achievement on the scale of *bent*, the negative pole of straightness. That scale has
    a least degree but no greatest, *slightly bent* against *??perfectly bent* ([kennedy-2007]
    (63) and p. 37), so the verb is atelic by default. -/
def bend : Verb where
  morphs := [.root "bend"]
  past := "bent"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .activity
  scaleDimension := some .straightness
  scalePolarity := .negative
  levinClasses := {LevinClass.assumePosition, .bend, .knead, .spatialConfiguration}

/-- "boil" — Levin 45.3 Cooking verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (reaches boiling point). -/
def boil : Verb where
  morphs := [.root "boil"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  scaleDimension := some .boiling
  levinClasses := {LevinClass.cooking, .prepare}

/-- "rust" — Levin 45.5 Entity-Specific CoS verbs. Inchoative only.
    Degree achievement: open scale (no maximum rustedness). -/
def rust : Verb where
  morphs := [.root "rust"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  scaleDimension := some .corrosion
  levinClasses := {LevinClass.entitySpecificChangeOfState, .entitySpecificModeOfBeing}

/-- "increase" — Levin 45.6 Calibratable CoS verbs (degree achievements).
    Degree achievement: open scale (no maximum quantity). -/
def increase : Verb where
  morphs := [.root "increase"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .activity
  scaleDimension := some .quantity
  levinClasses := {LevinClass.calibratableChangeOfState, .otherChangeOfState}

/-! ### Degree achievement verb pairs ([kennedy-2007]) -/

/-- "straighten" — Closed-scale degree achievement (base adj: straight).
    Accomplishment: "straightened the wire in 10 seconds." -/
def straighten : Verb where
  morphs := [.root "straighten"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  scaleDimension := some .straightness
  levinClasses := {LevinClass.otherChangeOfState}

/-- "flatten" — Closed-scale degree achievement (base adj: flat).
    Accomplishment: "flattened the dough in 2 minutes." -/
def flatten : Verb where
  morphs := [.root "flatten"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  scaleDimension := some .flatness
  levinClasses := {LevinClass.otherChangeOfState}

/-- "open" — Closed-scale degree achievement (base adj: open, closed scale).
    Accomplishment: "opened the door in 3 seconds." -/
def open_ : Verb where
  morphs := [.root "open"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .accomplishment
  scaleDimension := some .openness
  levinClasses := {LevinClass.appear, .crane, .otherChangeOfState, .spatialConfiguration}

/-- "lengthen" — Open-scale degree achievement (base adj: long, open scale).
    Activity: "lengthened the rope for hours." -/
def lengthen : Verb where
  morphs := [.root "lengthen"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .length
  levinClasses := {LevinClass.otherChangeOfState}

/-- "widen" — Open-scale degree achievement (base adj: wide, open scale).
    Activity: "widened the road for months." -/
def widen : Verb where
  morphs := [.root "widen"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .width
  levinClasses := {LevinClass.otherChangeOfState}

/-- "cool" — Open-scale degree achievement (base adj: cool, open scale).
    Activity: "cooled for an hour." -/
def cool : Verb where
  morphs := [.root "cool"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .temperature
  levinClasses := {LevinClass.otherChangeOfState}

/-- "warm" — Open-scale degree achievement (base adj: warm, open scale).
    Activity: "warmed for an hour." -/
def warm : Verb where
  morphs := [.root "warm"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .temperature
  levinClasses := {LevinClass.otherChangeOfState}

end English.Verbs
