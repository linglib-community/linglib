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

open ArgumentStructure Aspect Data.VerbClasses

/-! ### Physical disturbance change-of-state verbs ([tham-2025]) -/

/-- "crack" — Levin 45.1 Break verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale (contra [rappaport-hovav-2014] two-point
    classification), but allows BOTH telic ("cracked in a minute") and atelic
    ("cracked for two days") readings. Compatible with *completely*, *partially*,
    *badly*. The verb is NOT a standard degree achievement: its variable telicity
    does not reduce to scale boundedness alone. -/
def crack : Verb where
  morphs := [.root "crack"]
  levin := some Levin1993.Index.crack
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .achievement
  scaleDimension := some .cracking

/-- "dent" — Levin 21.2 Carve verbs. Physical disturbance CoS verb.
    [tham-2025]: closed scale, compatible with *more dented*, *completely
    dented*, *badly dented*. -/
def dent : Verb where
  morphs := [.root "dent"]
  levin := some Levin1993.Index.dent
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .achievement
  scaleDimension := some .denting

/-- "scratch" — Levin 21.1 Cut verbs, a physical disturbance CoS verb for
    [tham-2025]: closed scale, compatible with *more scratched*, *completely
    scratched*, *badly scratched*. Levin also lists it among the wipe verbs
    (§10.4.1) and the swat verbs (§18.2) on its manner readings. -/
def scratch : Verb where
  morphs := [.root "scratch"]
  levin := some Levin1993.Index.scratch
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .achievement
  scaleDimension := some .scratching

/-- "shatter" — Levin 45.1 Break verbs. NOT a physical disturbance verb.
    Punctual, non-gradable: *shatter in two minutes* (after, not duration),
    #*shatter for two minutes*, ??*more shattered* ([tham-2025] (12)). -/
def shatter : Verb where
  morphs := [.root "shatter"]
  levin := some Levin1993.Index.shatter
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .achievement

/-- "burn" — destruction or transformation by fire or heat; Levin 45.4 other change-of-state
    verbs. -/
def burn : Verb where
  morphs := [.root "burn"]
  levin := some Levin1993.Index.burn
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-- "destroy" — Levin 44 destroy verbs. -/
def destroy : Verb where
  morphs := [.root "destroy"]
  levin := some Levin1993.Index.destroy
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment

/-- "melt" — change of consistency by heat; Levin 45.4 other change-of-state verbs. A base
    transitive that takes a double-object benefactive ("melt me some ice cream") and an
    indefinite implicit object ("the ice cream melted" / "we're melting"). -/
def melt : Verb where
  morphs := [.root "melt"]
  levin := some Levin1993.Index.melt
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 3, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-! ### Further change-of-state verbs

The causative verbs Martin, Rose and Nichols survey that have no entry elsewhere in this
file. -/

/-- "activate" — sets a device or process in operation; not listed by Levin. -/
def activate : Verb where
  morphs := [.root "activate"]
  levin := none
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment


/-- "affect" — Levin 31.1 amuse verbs. -/
def affect : Verb where
  morphs := [.root "affect"]
  levin := some Levin1993.Index.affect
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity

/-- "change" — transformation; Levin 26.6 turn verbs. -/
def change : Verb where
  morphs := [.root "change"]
  levin := some Levin1993.Index.change
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.into) (some .transl), [0, 1, 2]),
     (⟨some .nominal, [.nominal, .adposition (some Adpositions.from_),
     .adposition (some Adpositions.into) (some .transl)]⟩, [0, 1, 3, 2])]
  vendlerClass := some .accomplishment

/-- "damage" — partial destruction; not listed by Levin. -/
def damage : Verb where
  morphs := [.root "damage"]
  levin := none
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment


/-- "eliminate" — removal; Levin 42.1 murder verbs. -/
def eliminate : Verb where
  morphs := [.root "eliminate"]
  levin := some Levin1993.Index.eliminate
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "hurt" — Levin 40.8.3 hurt verbs. -/
def hurt : Verb where
  morphs := [.root "hurt"]
  levin := some Levin1993.Index.hurt
  past := "hurt"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "restore" — Levin 13.2 contribute verbs. -/
def restore : Verb where
  morphs := [.root "restore"]
  levin := some Levin1993.Index.restore
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "trigger" — sets a process off; not listed by Levin. -/
def trigger : Verb where
  morphs := [.root "trigger"]
  levin := none
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement

/-- "bury" — covering with earth. Levin's concealment class (§16) does not list *bury*. -/
def bury : Verb where
  morphs := [.root "bury"]
  levin := none
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment


/-- "drop" — Levin 45.6 calibratable change-of-state verbs. -/
def drop : Verb where
  morphs := [.root "drop"]
  levin := some Levin1993.Index.drop
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment

/-- "lift" — Levin 9.4 verbs of putting with a specified direction. -/
def lift : Verb where
  morphs := [.root "lift"]
  levin := some Levin1993.Index.lift
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "lock" — securing with a lock; Levin lists *lock* only among the tape verbs (§22.4). -/
def lock : Verb where
  morphs := [.root "lock"]
  levin := some Levin1993.Index.lock
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment


/-- "shut" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def shut : Verb where
  morphs := [.root "shut"]
  levin := some Levin1993.Index.shut
  past := "shut"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment

/-- "spread" — Levin 9.7 spray/load verbs. -/
def spread : Verb where
  morphs := [.root "spread"]
  levin := some Levin1993.Index.spread
  past := "spread"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 2]),
     (ArgumentFrame.np_spatialPP, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 2, 1])]
  vendlerClass := some .accomplishment

/-- "stretch" — Levin 45.4 other change-of-state verbs. -/
def stretch : Verb where
  morphs := [.root "stretch"]
  levin := some Levin1993.Index.stretch
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .accomplishment

/-- "switch" — Levin's change-of-state lists do not include *switch*. -/
def switch : Verb where
  morphs := [.root "switch"]
  levin := none
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment


/-- "close" — Levin 45.4 other change-of-state verbs, zero-related to the adjective, and
    40.3.2 crane verbs (*close one's eyes*). -/
def close : Verb where
  morphs := [.root "close"]
  levin := some Levin1993.Index.close
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment

/-- "dry" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def dry : Verb where
  morphs := [.root "dry"]
  levin := some Levin1993.Index.dry
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  scaleDimension := some .wetness
  scalePolarity := .negative

/-- "enhance" — improvement in quality; not listed by Levin. -/
def enhance : Verb where
  morphs := [.root "enhance"]
  levin := none
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "extend" — Levin 47.1 exist verbs, 13.2 contribute verbs and 13.3 verbs of future
    having. -/
def extend : Verb where
  morphs := [.root "extend"]
  levin := some Levin1993.Index.extend
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment

/-- "lower" — Levin 9.4 verbs of putting with a specified direction. -/
def lower : Verb where
  morphs := [.root "lower"]
  levin := some Levin1993.Index.lower
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment

/-- "slow" — Levin 45.4 other change-of-state verbs, zero-related to the adjective. -/
def slow : Verb where
  morphs := [.root "slow"]
  levin := some Levin1993.Index.slow
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .activity
  scaleDimension := some .speed

/-- "turn" — Levin 26.6 turn verbs (*turn the prince into a frog*). -/
def turn : Verb where
  morphs := [.root "turn"]
  levin := some Levin1993.Index.turn
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.into) (some .transl), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinExcluded := {LevinClass.crane, .hurt, .meander, .roll}

/-- "wake up" — the particle verb of awakening; Levin lists *waken* but not *wake*. -/
def wakeUp : Verb where
  morphs := [.root "wake", .free "up"]
  levin := none
  past := "woke"
  pastPart := "woken"
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .achievement

/-! ### Change of State (§ 45) -/

/-- "freeze" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def freeze : Verb where
  morphs := [.root "freeze"]
  levin := some Levin1993.Index.freeze
  past := "froze"
  pastPart := "frozen"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .accomplishment

/-- "heat" — Levin 45.4 Other Change of State verbs. Causative/inchoative alternation. -/
def heat : Verb where
  morphs := [.root "heat"]
  levin := some Levin1993.Index.heat
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment

/-- "bend" — Levin 45.2 Bend verbs. Causative/inchoative alternation.
    Degree achievement on the scale of *bent*, the negative pole of straightness. That scale has
    a least degree but no greatest, *slightly bent* against *??perfectly bent* ([kennedy-2007]
    (63) and p. 37), so the verb is atelic by default. -/
def bend : Verb where
  morphs := [.root "bend"]
  levin := some Levin1993.Index.bend
  past := "bent"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .activity
  scaleDimension := some .straightness
  scalePolarity := .negative

/-- "boil" — Levin 45.3 Cooking verbs. Causative/inchoative alternation.
    Degree achievement: closed scale (reaches boiling point). -/
def boil : Verb where
  morphs := [.root "boil"]
  levin := some Levin1993.Index.boil
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  scaleDimension := some .boiling

/-- "rust" — Levin 45.5 Entity-Specific CoS verbs. Inchoative only.
    Degree achievement: open scale (no maximum rustedness). -/
def rust : Verb where
  morphs := [.root "rust"]
  levin := some Levin1993.Index.rust
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  scaleDimension := some .corrosion

/-- *increase* is a degree achievement on an open scale, with no maximum quantity. Levin lists it
with her other alternating verbs of change of state (45.4), whose transitive takes an agent or an
instrument subject, and with her verbs of calibratable change of state (45.6), which have no
transitive ([levin-1993] pp. 245, 247); its frames are those of the first. -/
def increase : Verb where
  morphs := [.root "increase"]
  levin := some Levin1993.Index.increase
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .quantity

/-! ### Degree achievement verb pairs ([kennedy-2007]) -/

/-- "straighten" — Closed-scale degree achievement (base adj: straight).
    Accomplishment: "straightened the wire in 10 seconds." -/
def straighten : Verb where
  morphs := [.root "straighten"]
  levin := some Levin1993.Index.straighten
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  scaleDimension := some .straightness

/-- "flatten" — Closed-scale degree achievement (base adj: flat).
    Accomplishment: "flattened the dough in 2 minutes." -/
def flatten : Verb where
  morphs := [.root "flatten"]
  levin := some Levin1993.Index.flatten
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  scaleDimension := some .flatness

/-- "open" — Closed-scale degree achievement (base adj: open, closed scale).
    Accomplishment: "opened the door in 3 seconds." -/
def open_ : Verb where
  morphs := [.root "open"]
  levin := some Levin1993.Index.«open»
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2])]
  vendlerClass := some .accomplishment
  scaleDimension := some .openness

/-- "lengthen" — Open-scale degree achievement (base adj: long, open scale).
    Activity: "lengthened the rope for hours." -/
def lengthen : Verb where
  morphs := [.root "lengthen"]
  levin := some Levin1993.Index.lengthen
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .length

/-- "widen" — Open-scale degree achievement (base adj: wide, open scale).
    Activity: "widened the road for months." -/
def widen : Verb where
  morphs := [.root "widen"]
  levin := some Levin1993.Index.widen
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .width

/-- "cool" — Open-scale degree achievement (base adj: cool, open scale).
    Activity: "cooled for an hour." -/
def cool : Verb where
  morphs := [.root "cool"]
  levin := some Levin1993.Index.cool
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .temperature

/-- "warm" — Open-scale degree achievement (base adj: warm, open scale).
    Activity: "warmed for an hour." -/
def warm : Verb where
  morphs := [.root "warm"]
  levin := some Levin1993.Index.warm
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .activity
  scaleDimension := some .temperature

end English.Verbs
