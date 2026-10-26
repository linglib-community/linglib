module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English verbs by Levin class

This file defines the English verbs entered under the smaller of Levin's classes, from putting
and removing through creation, perception, judgment, the body, emission, existence and
appearance, motion and weather, each with the frames Levin's alternations require.

## References

* [levin-1993]
* [degen-tonhauser-2022]
* [majid-boster-bowerman-2008]
* [smith-1997]
* [levin-hovav-1995]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree

/-! ### Putting (§ 9) -/

/-- "place" — Levin 9.1 Put verbs. Instantaneous placement. -/
def place : Verb where
  morphs := [.root "place"]
  valency := .ofFrame ArgumentFrame.np_pp
  vendlerClass := some .achievement
  levinClasses := {LevinClass.put}

/-- "water" — Levin 9.9 Butter verbs (denominal putting). -/
def water : Verb where
  morphs := [.root "water"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  levinClasses := {LevinClass.butter}

/-- "pour" — Levin 9.5 Pour verbs. Manner of caused motion. -/
def pour : Verb where
  morphs := [.root "pour"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.pour, .prepare, .substanceEmission, .weather}

/-- "spray" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def spray : Verb where
  morphs := [.root "spray"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 2]),
     (ArgumentFrame.np_spatialPP, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.sprayLoad}

/-- "load" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def load : Verb where
  morphs := [.root "load"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 2]),
     (ArgumentFrame.np_spatialPP, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.sprayLoad}

/-! ### Removing (§ 10) -/

/-- "remove" — Levin 10.1 Remove verbs. -/
def remove : Verb where
  morphs := [.root "remove"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.banish, .remove}

/-- "clean" — Levin 10.3 Clear verbs. Incremental by surface area.
    Also a degree achievement: closed scale (maximally clean). -/
def clean : Verb where
  morphs := [.root "clean"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_spatialPP, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .accomplishment
  scaleDimension := some .cleanliness
  incrementality := some .strict
  levinClasses := {LevinClass.clear, .otherChangeOfState, .prepare}

/-- "steal" — Levin 10.5 Steal verbs. -/
def steal : Verb where
  morphs := [.root "steal"]
  past := "stole"
  pastPart := "stolen"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.appear, .get, .steal}

/-! ### Sending and Carrying (§ 11) -/

/-- "send" — Levin 11.1 Send verbs. Alternates DOC/PP.
    Goal does not entail possession (prospective). The PP may be implicit, a definite; the
    theme may not ([bruening-2021]). -/
def send : Verb where
  morphs := [.root "send"]
  past := "sent"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     ((ArgumentFrame.np_pp (some Adpositions.to_) (some .dat)).leaveImplicit 1 (some .def),
       [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.send}

/-- "drive" — Levin 11.5 Drive verbs (vehicle-mediated motion). -/
def drive : Verb where
  morphs := [.root "drive"]
  past := "drove"
  pastPart := "driven"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.drive, .nonVehicleName}

/-! ### Change of Possession (§ 13) -/

/-- "donate" — Levin 13.2 Contribute verbs. -/
def donate : Verb where
  morphs := [.root "donate"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.contribute}

/-- "obtain" — Levin 13.5.2 Obtain verbs. -/
def obtain : Verb where
  morphs := [.root "obtain"]
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.for_) (some .ben)]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.obtain}

/-- "trade" — Levin 13.6 Exchange verbs. -/
def trade : Verb where
  morphs := [.root "trade"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement
  levinClasses := {LevinClass.exchange, .give}

/-! ### Learn, Hold, Conceal (§ 14–16) -/

/-- "learn" — Levin 14 Learn verbs. -/
def learn : Verb where
  morphs := [.root "learn"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.learn}

/-- "hold" — Levin 15.1 Hold verbs. Stative. -/
def hold : Verb where
  morphs := [.root "hold"]
  past := "held"
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.on) (some .sup)]
  vendlerClass := some .state
  levinClasses := {LevinClass.conjecture, .fit, .hold}

/-- "hide" — Levin 16 Conceal verbs. -/
def hide : Verb where
  morphs := [.root "hide"]
  past := "hid"
  pastPart := "hidden"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.conceal}

/-! ### Throwing (§ 17) -/

/-- "throw" — Levin 17.1 Throw verbs. Ballistic motion. Alternates DOC/PP.
    Implicit DO in PP frame only (definite). -/
def throw : Verb where
  morphs := [.root "throw"]
  past := "threw"
  pastPart := "thrown"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     ((ArgumentFrame.np_pp (some Adpositions.to_) (some .dat)).leaveImplicit 0 (some .def),
       [0, 1, 2]),
     ((ArgumentFrame.np_pp (some Adpositions.to_) (some .dat)).leaveImplicit 1 (some .indef),
       [0, 1, 2])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amuse, .throw}

/-! ### Contact (§ 19–20) -/

/-- "poke" — Levin 19 Poke verbs. Punctual contact. -/
def poke : Verb where
  morphs := [.root "poke"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.poke, .rummage}

/-- "touch" — Levin 20 Touch verbs. Surface contact. -/
def touch : Verb where
  morphs := [.root "touch"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amuse, .contiguousLocation, .touch}

/-! ### Cutting (§ 21) -/

/-- "cut" — Levin 21.1 Cut verbs. Incremental by length of cut.
    [majid-boster-bowerman-2008] place cutting at the predictable end of their first
    dimension, a sharp instrument pressed into a firm but yielding object. -/
def cut : Verb where
  morphs := [.root "cut"]
  past := "cut"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  root := { content := {
    resultGeometry := {.surfaceBreach}
    instrument := {.sharpBlade}
  } }
  levinClasses := {LevinClass.amuse, .braid, .build, .cut, .hurt, .meander, .split}

/-- "chop" — Levin 21.2 Carve verbs. -/
def chop : Verb where
  morphs := [.root "chop"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.carve}

/-! ### Combining and Separating (§ 22–23) -/

/-- "mix" — Levin 22.1 Mix verbs. Incremental by proportion combined. -/
def mix : Verb where
  morphs := [.root "mix"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.correspond, .mix, .prepare}

/-- "separate" — Levin 23.1 Separate verbs. -/
def separate : Verb where
  morphs := [.root "separate"]
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.remove, .separate}

/-! ### Coloring and Image Creation (§ 24–25) -/

/-- "paint" — Levin 24 Color verbs. Incremental by surface area. -/
def paint : Verb where
  morphs := [.root "paint"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.characterize, .color, .imageImpression, .performance, .scribble}

/-- "draw" — Levin 25 Image Creation verbs. Incremental by extent. -/
def draw : Verb where
  morphs := [.root "draw"]
  past := "drew"
  pastPart := "drawn"
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef)]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.performance, .pushPull, .remove, .scribble, .split}

/-! ### Creation and Transformation (§ 26) -/

/-- "create" — Levin 26.4 Create verbs. -/
def create : Verb where
  morphs := [.root "create"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.create, .engender}

/-- "weave" — Levin 26.1 Build verbs. -/
def weave : Verb where
  morphs := [.root "weave"]
  past := "wove"
  pastPart := "woven"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_) (some .ben), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.out), [0, 1, 3]),
     (ArgumentFrame.np_pp (some Adpositions.into) (some .transl), [0, 3, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.build, .meander}

/-- "grow" — Levin 26.2 Grow verbs. Incremental by size. -/
def grow : Verb where
  morphs := [.root "grow"]
  past := "grew"
  pastPart := "grown"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.out), [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.into) (some .transl), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict
  levinClasses := {LevinClass.appear, .build, .calibratableChangeOfState,
    .entitySpecificModeOfBeing, .grow, .otherChangeOfState}

/-- "perform" — Levin 26.7 Performance verbs. -/
def perform : Verb where
  morphs := [.root "perform"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_) (some .ben), [0, 1, 2])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.performance}

/-! ### Predicative Complements (§ 29) -/

/-- "appoint" — Levin 29.1 Appoint verbs. -/
def appoint : Verb where
  morphs := [.root "appoint"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appoint}

/-! ### Perception (§ 30) -/

/-- "hear" — Levin 30.1 See verbs. Stative perception. Also embeds
    finite clauses (optionally factive per [degen-tonhauser-2022]). -/
def hear : Verb where
  morphs := [.root "hear"]
  past := "heard"
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.finiteClause]
  vendlerClass := some .state
  levinClasses := {LevinClass.see}

/-! ### Judgment and Assessment (§ 33–34) -/

/-- "blame" — a judgment verb by sense, absent from Levin's §33 member lists
    and named only for the blame alternation (§2.10). -/
def blame : Verb where
  morphs := [.root "blame"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative


/-- "evaluate" — Levin 34 Assessment verbs. -/
def evaluate : Verb where
  morphs := [.root "evaluate"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative
  levinClasses := {LevinClass.assessment}

/-! ### Social Interaction (§ 36) -/

/-- "marry" — Levin 36 Social Interaction verbs. -/
def marry : Verb where
  morphs := [.root "marry"]
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.objectDrop (some .reciprocal)]
  vendlerClass := some .achievement
  levinClasses := {LevinClass.amalgamate, .marry}

/-! ### Animal Sounds (§ 38) -/

/-- "bark" — Levin 38 Animal Sound verbs. -/
def bark : Verb where
  morphs := [.root "bark"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .hurt, .mannerOfSpeaking, .pit}

/-! ### Body (§ 40–41) -/

/-- "breathe" — Levin 40.1 Body Process verbs. -/
def breathe : Verb where
  morphs := [.root "breathe"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .entitySpecificModeOfBeing}

/-- "laugh" — Levin 40.2 Nonverbal Expression verbs. -/
def laugh : Verb where
  morphs := [.root "laugh"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonverbalExpression}

/-- "cough" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary event, no result state ([smith-1997] §2.4.3). -/
def cough : Verb where
  morphs := [.root "cough"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.breathe, .nonverbalExpression}

/-- "hiccup" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary body event ([smith-1997] §2.4.3). -/
def hiccup : Verb where
  morphs := [.root "hiccup"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hiccup}

/-- "blink" — a semelfactive, a single instantaneous eye movement by [smith-1997]'s
    characterization of the class. Levin lists *blink (eye)* among the wink verbs (§40.3.1)
    and *blink* among the light-emission verbs (§43.1); this entry is the eye movement, a
    class the library does not name. -/
def blink : Verb where
  morphs := [.root "blink"]
  valency := .ofFrames
    [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.objectDrop (some .bodyPart)]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.wink}
  levinExcluded := {LevinClass.lightEmission}

/-- "knock" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single percussive contact event, [smith-1997]'s standard
    example of the class. -/
def knock : Verb where
  morphs := [.root "knock"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hit, .nonAgentiveImpact, .soundEmission, .split, .throw}

/-- "tap" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single light percussive contact event ([smith-1997] §2.4.3). -/
def tap : Verb where
  morphs := [.root "tap"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.hit, .investigate, .throw}

/-- "flash" — Levin 43.1 Light Emission verbs.
    Semelfactive: single instantaneous light event, by [smith-1997]'s
    characterization of the class. -/
def flash : Verb where
  morphs := [.root "flash"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .semelfactive
  levinClasses := {LevinClass.crane, .lightEmission}

/-- "flinch" — Levin 40.5 Flinch verbs. Involuntary reaction. -/
def flinch : Verb where
  morphs := [.root "flinch"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.flinch}

/-- "dress" — Levin 41.1 Dress verbs. -/
def dress : Verb where
  morphs := [.root "dress"]
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.objectDrop (some .reflexive), [0, 1])]
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.dress, .dressingWell}

/-! ### Killing (§ 42) -/

/-- "drown" — Levin 42.2 Poison verbs. Manner-of-killing. -/
def drown : Verb where
  morphs := [.root "drown"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  levinClasses := {LevinClass.poison, .suffocate}

/-! ### Emission (§ 43) -/

/-- *glow*, a verb of light emission. Among these only *beam*, *shine* and *flash* have a causative
use ([levin-hovav-1995] p. 116), so the entry records none. -/
def glow : Verb where
  morphs := [.root "glow"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.spatialPP, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.with_), [1, 0])]
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.lightEmission}

/-- "buzz" — Levin 43.2 Sound Emission verbs. -/
def buzz : Verb where
  morphs := [.root "buzz"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .soundEmission}

/-- "rumble" — Levin 43.2 Sound Emission verbs. -/
def rumble : Verb where
  morphs := [.root "rumble"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission}

/-- "bleed" — Levin 43.4 Substance Emission verbs. -/
def bleed : Verb where
  morphs := [.root "bleed"]
  past := "bled"
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.pp (some Adpositions.from_) (some .abl), [0, 1])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .cheat, .marvel, .substanceEmission}

/-! ### Existence, Appearance, Position (§ 47–50) -/

/-- *exist*, an unaccusative stative verb of existence (47.1). -/
def exist : Verb where
  morphs := [.root "exist"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.exist, .gorge}

/-- *appear*, an unaccusative verb of appearance (48.1.1). -/
def appear : Verb where
  morphs := [.root "appear"]
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic
  passivizable := false
  vendlerClass := some .achievement
  levinClasses := {LevinClass.appear}

/-- "fidget" — Levin 49 Body-Internal Motion verbs. -/
def fidget : Verb where
  morphs := [.root "fidget"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.bodyInternalMotion}

/-- "wiggle" — Levin 47.3 Modes of Being Involving Motion and 49 Body-Internal Motion verbs;
    transitive with a body part or small object ("wiggle a tooth"). -/
def wiggle : Verb where
  morphs := [.root "wiggle"]
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.np, [1, 0])]
  vendlerClass := some .activity
  levinClasses := {LevinClass.modeOfBeingInvolvingMotion, .bodyInternalMotion, .crane}

/-- "wriggle" — Levin 49 Body-Internal Motion verbs. -/
def wriggle : Verb where
  morphs := [.root "wriggle"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.bodyInternalMotion}

/-- "sit" — Levin 50 Assume Position verbs. Stative. -/
def sit : Verb where
  morphs := [.root "sit"]
  past := "sat"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.assumePosition, .putInSpatialConfiguration, .spatialConfiguration}

/-- "stand" — Levin 50 Assume Position verbs. Stative. -/
def stand : Verb where
  morphs := [.root "stand"]
  past := "stood"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state
  levinClasses := {LevinClass.admire, .assumePosition, .putInSpatialConfiguration,
    .spatialConfiguration}

/-! ### Motion (§ 51) -/

/-- "walk" — Levin 51.3 Manner of Motion verbs. -/
def walk : Verb where
  morphs := [.root "walk"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2])]
    [some activitySubjectProfile, none, none]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place
  levinClasses := {LevinClass.run}

/-- *swim*, an agentive verb of manner of motion, whose causative takes a directional phrase as
the causatives of all such verbs do ([levin-hovav-1995] p. 111). -/
def swim : Verb where
  morphs := [.root "swim"]
  past := "swam"
  pastPart := "swum"
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np_spatialPP, [1, 0, 2]),
     (ArgumentFrame.spatialPP, [0, 2])]
    [some activitySubjectProfile, none, none]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place
  levinClasses := {LevinClass.run, .swarm, .tingle}

/-- "fly" — Levin 51.4 Vehicle Motion verbs. -/
def fly : Verb where
  morphs := [.root "fly"]
  past := "flew"
  pastPart := "flown"
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.drive, .nonVehicleName, .run, .spatialConfiguration}

/-- "roll" — Levin 51.3.1 Roll verbs (manner of motion). -/
def roll : Verb where
  morphs := [.root "roll"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2])]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place
  levinClasses := {LevinClass.build, .coil, .crane, .prepare, .roll, .run, .shake, .slide,
    .soundEmission, .split}

/-- "float" — Levin 51.3.1 Roll verbs (manner of motion). -/
def float : Verb where
  morphs := [.root "float"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.modeOfBeingInvolvingMotion, .roll, .run, .slide}

/-! ### Avoid, Linger, Rush (§ 52–53) -/

/-- "avoid" — Levin 52 Avoid verbs. Stative. -/
def avoid : Verb where
  morphs := [.root "avoid"]
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state
  levinClasses := {LevinClass.avoid}

/-- "linger" — Levin 53.1 Linger verbs. -/
def linger : Verb where
  morphs := [.root "linger"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.exist, .linger}

/-- "rush" — Levin 53.2 Rush verbs. -/
def rush : Verb where
  morphs := [.root "rush"]
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.run, .rush}

/-! ### Weather (§ 57) -/

/-- "rain" — Levin 57 Weather verbs. Expletive subject. -/
def rain : Verb where
  morphs := [.root "rain"]
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity
  levinClasses := {LevinClass.weather}

end English.Verbs
