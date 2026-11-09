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

open ArgumentStructure Aspect Data.VerbClasses

/-! ### Putting (§ 9) -/

/-- "place" — Levin 9.1 Put verbs. Instantaneous placement. -/
def place : Verb where
  morphs := [.root "place"]
  levin := some Levin1993.Index.place
  valency := .ofFrame ArgumentFrame.np_pp
  vendlerClass := some .achievement

/-- "water" — Levin 9.9 Butter verbs (denominal putting). -/
def water : Verb where
  morphs := [.root "water"]
  levin := some Levin1993.Index.water
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity

/-- "pour" — Levin 9.5 Pour verbs. Manner of caused motion. -/
def pour : Verb where
  morphs := [.root "pour"]
  levin := some Levin1993.Index.pour
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .activity
  incrementality := some .cumulative

/-- "spray" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def spray : Verb where
  morphs := [.root "spray"]
  levin := some Levin1993.Index.spray
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 2]),
     (ArgumentFrame.np_spatialPP, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-- "load" — Levin 9.7 Spray/Load verbs. Locative alternation. -/
def load : Verb where
  morphs := [.root "load"]
  levin := some Levin1993.Index.load
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 2]),
     (ArgumentFrame.np_spatialPP, [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.with_), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-! ### Removing (§ 10) -/

/-- "remove" — Levin 10.1 Remove verbs. -/
def remove : Verb where
  morphs := [.root "remove"]
  levin := some Levin1993.Index.remove
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "clean" — Levin 10.3 Clear verbs. Incremental by surface area.
    Also a degree achievement: closed scale (maximally clean). -/
def clean : Verb where
  morphs := [.root "clean"]
  levin := some Levin1993.Index.clean
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_spatialPP, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .accomplishment
  scaleDimension := some .cleanliness
  incrementality := some .strict

/-- "steal" — Levin 10.5 Steal verbs. -/
def steal : Verb where
  morphs := [.root "steal"]
  levin := some Levin1993.Index.steal
  past := "stole"
  pastPart := "stolen"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-! ### Sending and Carrying (§ 11) -/

/-- "send" — Levin 11.1 Send verbs. Alternates DOC/PP.
    Goal does not entail possession (prospective). The PP may be implicit, a definite; the
    theme may not ([bruening-2021]). -/
def send : Verb where
  morphs := [.root "send"]
  levin := some Levin1993.Index.send
  past := "sent"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     ((ArgumentFrame.np_pp (some Adpositions.to_) (some .dat)).leaveImplicit 1 (some .def),
       [0, 1, 2])]
  vendlerClass := some .accomplishment

/-- "drive" — Levin 11.5 Drive verbs (vehicle-mediated motion). -/
def drive : Verb where
  morphs := [.root "drive"]
  levin := some Levin1993.Index.drive
  past := "drove"
  pastPart := "driven"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative

/-! ### Change of Possession (§ 13) -/

/-- "donate" — Levin 13.2 Contribute verbs. -/
def donate : Verb where
  morphs := [.root "donate"]
  levin := some Levin1993.Index.donate
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "obtain" — Levin 13.5.2 Obtain verbs. -/
def obtain : Verb where
  morphs := [.root "obtain"]
  levin := some Levin1993.Index.obtain
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.for_) (some .ben)]
  vendlerClass := some .accomplishment

/-- "trade" — Levin 13.6 Exchange verbs. -/
def trade : Verb where
  morphs := [.root "trade"]
  levin := some Levin1993.Index.trade
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement

/-! ### Learn, Hold, Conceal (§ 14–16) -/

/-- "learn" — Levin 14 Learn verbs. -/
def learn : Verb where
  morphs := [.root "learn"]
  levin := some Levin1993.Index.learn
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "hold" — Levin 15.1 Hold verbs. Stative. -/
def hold : Verb where
  morphs := [.root "hold"]
  levin := some Levin1993.Index.hold
  past := "held"
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.np_pp (some Adpositions.on) (some .sup)]
  vendlerClass := some .state

/-- "hide" — Levin 16 Conceal verbs. -/
def hide : Verb where
  morphs := [.root "hide"]
  levin := some Levin1993.Index.hide
  past := "hid"
  pastPart := "hidden"
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-! ### Throwing (§ 17) -/

/-- "throw" — Levin 17.1 Throw verbs. Ballistic motion. Alternates DOC/PP.
    Implicit DO in PP frame only (definite). -/
def throw : Verb where
  morphs := [.root "throw"]
  levin := some Levin1993.Index.throw
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

/-! ### Contact (§ 19–20) -/

/-- "poke" — Levin 19 Poke verbs. Punctual contact. -/
def poke : Verb where
  morphs := [.root "poke"]
  levin := some Levin1993.Index.poke
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .achievement

/-- "touch" — Levin 20 Touch verbs. Surface contact. -/
def touch : Verb where
  morphs := [.root "touch"]
  levin := some Levin1993.Index.touch
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .achievement

/-! ### Cutting (§ 21) -/

/-- "cut" — Levin 21.1 Cut verbs. Incremental by length of cut.
    [majid-boster-bowerman-2008] place cutting at the predictable end of their first
    dimension, a sharp instrument pressed into a firm but yielding object. -/
def cut : Verb where
  morphs := [.root "cut"]
  levin := some Levin1993.Index.cut
  past := "cut"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-- "chop" — Levin 21.2 Carve verbs. -/
def chop : Verb where
  morphs := [.root "chop"]
  levin := some Levin1993.Index.chop
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 2]),
     (ArgumentFrame.np, [2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-! ### Combining and Separating (§ 22–23) -/

/-- "mix" — Levin 22.1 Mix verbs. Incremental by proportion combined. -/
def mix : Verb where
  morphs := [.root "mix"]
  levin := some Levin1993.Index.mix
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-- "separate" — Levin 23.1 Separate verbs. -/
def separate : Verb where
  morphs := [.root "separate"]
  levin := some Levin1993.Index.separate
  valency := .of [(ArgumentFrame.np, [0, 1]), (ArgumentFrame.intransitive, [1])]
  vendlerClass := some .accomplishment

/-! ### Coloring and Image Creation (§ 24–25) -/

/-- "paint" — Levin 24 Color verbs. Incremental by surface area. -/
def paint : Verb where
  morphs := [.root "paint"]
  levin := some Levin1993.Index.paint
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-- "draw" — Levin 25 Image Creation verbs. Incremental by extent. -/
def draw : Verb where
  morphs := [.root "draw"]
  levin := some Levin1993.Index.draw
  past := "drew"
  pastPart := "drawn"
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.objectDrop (some .indef)]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-! ### Creation and Transformation (§ 26) -/

/-- "create" — Levin 26.4 Create verbs. -/
def create : Verb where
  morphs := [.root "create"]
  levin := some Levin1993.Index.create
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-- "weave" — Levin 26.1 Build verbs. -/
def weave : Verb where
  morphs := [.root "weave"]
  levin := some Levin1993.Index.weave
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

/-- "grow" — Levin 26.2 Grow verbs. Incremental by size. -/
def grow : Verb where
  morphs := [.root "grow"]
  levin := some Levin1993.Index.grow
  past := "grew"
  pastPart := "grown"
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.np_pp (some Adpositions.out), [0, 1, 2]),
     (ArgumentFrame.np_pp (some Adpositions.into) (some .transl), [0, 2, 1])]
  vendlerClass := some .accomplishment
  incrementality := some .strict

/-- "perform" — Levin 26.7 Performance verbs. -/
def perform : Verb where
  morphs := [.root "perform"]
  levin := some Levin1993.Index.perform
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.objectDrop (some .indef), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.for_) (some .ben), [0, 1, 2])]
  vendlerClass := some .accomplishment

/-! ### Predicative Complements (§ 29) -/

/-- "appoint" — Levin 29.1 Appoint verbs. -/
def appoint : Verb where
  morphs := [.root "appoint"]
  levin := some Levin1993.Index.appoint
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .achievement

/-! ### Perception (§ 30) -/

/-- "hear" — Levin 30.1 See verbs. Stative perception. Also embeds
    finite clauses (optionally factive per [degen-tonhauser-2022]). -/
def hear : Verb where
  morphs := [.root "hear"]
  levin := some Levin1993.Index.hear
  past := "heard"
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.finiteClause]
  vendlerClass := some .state

/-! ### Judgment and Assessment (§ 33–34) -/

/-- "blame" — a judgment verb by sense, absent from Levin's §33 member lists
    and named only for the blame alternation (§2.10). -/
def blame : Verb where
  morphs := [.root "blame"]
  levin := none
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative


/-- "evaluate" — Levin 34 Assessment verbs. -/
def evaluate : Verb where
  morphs := [.root "evaluate"]
  levin := some Levin1993.Index.evaluate
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .activity
  incrementality := some .cumulative

/-! ### Social Interaction (§ 36) -/

/-- "marry" — Levin 36 Social Interaction verbs. -/
def marry : Verb where
  morphs := [.root "marry"]
  levin := some Levin1993.Index.marry
  valency := .ofFrames [ArgumentFrame.np, ArgumentFrame.objectDrop (some .reciprocal)]
  vendlerClass := some .achievement

/-! ### Animal Sounds (§ 38) -/

/-- "bark" — Levin 38 Animal Sound verbs. -/
def bark : Verb where
  morphs := [.root "bark"]
  levin := some Levin1993.Index.bark
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity

/-! ### Body (§ 40–41) -/

/-- "breathe" — Levin 40.1 Body Process verbs. -/
def breathe : Verb where
  morphs := [.root "breathe"]
  levin := some Levin1993.Index.breathe
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity

/-- "laugh" — Levin 40.2 Nonverbal Expression verbs. -/
def laugh : Verb where
  morphs := [.root "laugh"]
  levin := some Levin1993.Index.laugh
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity

/-- "cough" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary event, no result state ([smith-1997] §2.4.3). -/
def cough : Verb where
  morphs := [.root "cough"]
  levin := some Levin1993.Index.cough
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .semelfactive

/-- "hiccup" — Levin 40.1 Body Process verbs.
    Semelfactive: single involuntary body event ([smith-1997] §2.4.3). -/
def hiccup : Verb where
  morphs := [.root "hiccup"]
  levin := some Levin1993.Index.hiccup
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .semelfactive

/-- "blink" — a semelfactive, a single instantaneous eye movement by [smith-1997]'s
    characterization of the class. Levin lists *blink (eye)* among the wink verbs (§40.3.1)
    and *blink* among the light-emission verbs (§43.1); this entry is the eye movement, a
    class the library does not name. -/
def blink : Verb where
  morphs := [.root "blink"]
  levin := some Levin1993.Index.blink
  valency := .ofFrames
    [ArgumentFrame.intransitive, ArgumentFrame.np, ArgumentFrame.objectDrop (some .bodyPart)]
  passivizable := false
  vendlerClass := some .semelfactive
  levinExcluded := {LevinClass.lightEmission}

/-- "knock" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single percussive contact event, [smith-1997]'s standard
    example of the class. -/
def knock : Verb where
  morphs := [.root "knock"]
  levin := some Levin1993.Index.knock
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  passivizable := false
  vendlerClass := some .semelfactive

/-- "tap" — Levin 18.1 Hit verbs (intransitive use).
    Semelfactive: single light percussive contact event ([smith-1997] §2.4.3). -/
def tap : Verb where
  morphs := [.root "tap"]
  levin := some Levin1993.Index.tap
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.at_), [0, 1]),
     (ArgumentFrame.np_pp (some Adpositions.on) (some .sup), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.with_) (some .inst), [0, 1, 3])]
  passivizable := false
  vendlerClass := some .semelfactive

/-- "flash" — Levin 43.1 Light Emission verbs.
    Semelfactive: single instantaneous light event, by [smith-1997]'s
    characterization of the class. -/
def flash : Verb where
  morphs := [.root "flash"]
  levin := some Levin1993.Index.flash
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .semelfactive

/-- "flinch" — Levin 40.5 Flinch verbs. Involuntary reaction. -/
def flinch : Verb where
  morphs := [.root "flinch"]
  levin := some Levin1993.Index.flinch
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .achievement

/-- "dress" — Levin 41.1 Dress verbs. -/
def dress : Verb where
  morphs := [.root "dress"]
  levin := some Levin1993.Index.dress
  valency := .of
    [(ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1]),
     (ArgumentFrame.objectDrop (some .reflexive), [0, 1])]
  vendlerClass := some .accomplishment

/-! ### Killing (§ 42) -/

/-- "drown" — Levin 42.2 Poison verbs. Manner-of-killing. -/
def drown : Verb where
  morphs := [.root "drown"]
  levin := some Levin1993.Index.drown
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .accomplishment

/-! ### Emission (§ 43) -/

/-- *glow*, a verb of light emission. Among these only *beam*, *shine* and *flash* have a causative
use ([levin-hovav-1995] p. 116), so the entry records none. -/
def glow : Verb where
  morphs := [.root "glow"]
  levin := some Levin1993.Index.glow
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.spatialPP, [0, 1]),
     (ArgumentFrame.pp (some Adpositions.with_), [1, 0])]
  passivizable := false
  vendlerClass := some .state

/-- "buzz" — Levin 43.2 Sound Emission verbs. -/
def buzz : Verb where
  morphs := [.root "buzz"]
  levin := some Levin1993.Index.buzz
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .activity

/-- "rumble" — Levin 43.2 Sound Emission verbs. -/
def rumble : Verb where
  morphs := [.root "rumble"]
  levin := some Levin1993.Index.rumble
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2]),
     (ArgumentFrame.pp (some Adpositions.with_), [2, 0])]
  passivizable := false
  vendlerClass := some .activity

/-- "bleed" — Levin 43.4 Substance Emission verbs. -/
def bleed : Verb where
  morphs := [.root "bleed"]
  levin := some Levin1993.Index.bleed
  past := "bled"
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.pp (some Adpositions.from_) (some .abl), [0, 1])]
  passivizable := false
  vendlerClass := some .activity

/-! ### Existence, Appearance, Position (§ 47–50) -/

/-- *exist*, an unaccusative stative verb of existence (47.1). -/
def exist : Verb where
  morphs := [.root "exist"]
  levin := some Levin1993.Index.exist
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic
  passivizable := false
  vendlerClass := some .state

/-- *appear*, an unaccusative verb of appearance (48.1.1). -/
def appear : Verb where
  morphs := [.root "appear"]
  levin := some Levin1993.Index.appear
  valency := .ofFrame ArgumentFrame.intransitive
  voiceType := some .nonThematic
  passivizable := false
  vendlerClass := some .achievement

/-- "fidget" — Levin 49 Body-Internal Motion verbs. -/
def fidget : Verb where
  morphs := [.root "fidget"]
  levin := some Levin1993.Index.fidget
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity

/-- "wiggle" — Levin 47.3 Modes of Being Involving Motion and 49 Body-Internal Motion verbs;
    transitive with a body part or small object ("wiggle a tooth"). -/
def wiggle : Verb where
  morphs := [.root "wiggle"]
  levin := some Levin1993.Index.wiggle
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.np, [1, 0])]
  vendlerClass := some .activity

/-- "wriggle" — Levin 49 Body-Internal Motion verbs. -/
def wriggle : Verb where
  morphs := [.root "wriggle"]
  levin := some Levin1993.Index.wriggle
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity

/-- "sit" — Levin 50 Assume Position verbs. Stative. -/
def sit : Verb where
  morphs := [.root "sit"]
  levin := some Levin1993.Index.sit
  past := "sat"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state

/-- "stand" — Levin 50 Assume Position verbs. Stative. -/
def stand : Verb where
  morphs := [.root "stand"]
  levin := some Levin1993.Index.stand
  past := "stood"
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .state

/-! ### Motion (§ 51) -/

/-- "walk" — Levin 51.3 Manner of Motion verbs. -/
def walk : Verb where
  morphs := [.root "walk"]
  levin := some Levin1993.Index.walk
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2])]
    [some activitySubjectProfile, none, none]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place

/-- *swim*, an agentive verb of manner of motion, whose causative takes a directional phrase as
the causatives of all such verbs do ([levin-hovav-1995] p. 111). -/
def swim : Verb where
  morphs := [.root "swim"]
  levin := some Levin1993.Index.swim
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

/-- "fly" — Levin 51.4 Vehicle Motion verbs. -/
def fly : Verb where
  morphs := [.root "fly"]
  levin := some Levin1993.Index.fly
  past := "flew"
  pastPart := "flown"
  valency := .of [(ArgumentFrame.intransitive, [0]), (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity

/-- "roll" — Levin 51.3.1 Roll verbs (manner of motion). -/
def roll : Verb where
  morphs := [.root "roll"]
  levin := some Levin1993.Index.roll
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0]),
     (ArgumentFrame.spatialPP, [0, 2])]
  passivizable := false
  vendlerClass := some .activity
  direction := some .place

/-- "float" — Levin 51.3.1 Roll verbs (manner of motion). -/
def float : Verb where
  morphs := [.root "float"]
  levin := some Levin1993.Index.float
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity

/-! ### Avoid, Linger, Rush (§ 52–53) -/

/-- "avoid" — Levin 52 Avoid verbs. Stative. -/
def avoid : Verb where
  morphs := [.root "avoid"]
  levin := some Levin1993.Index.avoid
  valency := .ofFrame ArgumentFrame.np
  vendlerClass := some .state

/-- "linger" — Levin 53.1 Linger verbs. -/
def linger : Verb where
  morphs := [.root "linger"]
  levin := some Levin1993.Index.linger
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity

/-- "rush" — Levin 53.2 Rush verbs. -/
def rush : Verb where
  morphs := [.root "rush"]
  levin := some Levin1993.Index.rush
  valency := .of
    [(ArgumentFrame.intransitive, [0]),
     (ArgumentFrame.np, [1, 0])]
  passivizable := false
  vendlerClass := some .activity

/-! ### Weather (§ 57) -/

/-- "rain" — Levin 57 Weather verbs. Expletive subject. -/
def rain : Verb where
  morphs := [.root "rain"]
  levin := some Levin1993.Index.rain
  valency := .ofFrame ArgumentFrame.intransitive
  passivizable := false
  vendlerClass := some .activity

end English.Verbs
