module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English communication verbs

This file defines the English verbs of communication, *say*, *tell* and *claim*, and Levin's
manner-of-speaking class, *whisper*, *shout*, *mumble* and the rest, with *speak* and *talk*.

## References

* [bruening-2021]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Data.VerbClasses

/-! ### Communication -/

/-- "say" — communication verb, not factive -/
def say : Verb where
  morphs := [.root "say"]
  levin := some Levin1993.Index.say
  past := "said"
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement

/-- "tell" — communication verb with recipient.
    Also ditransitive ("tell me a story"). The direct object may be implicit in the double
    object frame only, a definite (*Tell me*, but not *told to me*); the PP may be implicit, an
    indefinite ([bruening-2021]). -/
def tell : Verb where
  morphs := [.root "tell"]
  levin := some Levin1993.Index.tell
  past := "told"
  speechActVerb := true
  valency := .of
    [(ArgumentFrame.finiteClause, [0, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .def), [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     ((ArgumentFrame.np_pp (some Adpositions.to_) (some .dat)).leaveImplicit 1 (some .indef),
       [0, 1, 2])]
  vendlerClass := some .achievement

/-- "claim" — communication verb, speaker doesn't endorse. It takes a finite clause or an
infinitive its subject controls (*claimed to be rich*). -/
def claim : Verb where
  morphs := [.root "claim"]
  levin := some Levin1993.Index.claim
  speechActVerb := true
  valency := .ofFrames [.finiteClause, toInfinitive] (controllers := [none, some 0])
  vendlerClass := some .achievement

/-! ### Manner of Speaking (Levin 37.3)

Manner-of-speaking verbs specify how something is said. -/

/-- "whisper" — Levin 37.3 Manner of Speaking verbs. -/
def whisper : Verb where
  morphs := [.root "whisper"]
  levin := some Levin1993.Index.whisper
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "murmur" — Levin 37.3 Manner of Speaking verbs. -/
def murmur : Verb where
  morphs := [.root "murmur"]
  levin := some Levin1993.Index.murmur
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "shout" — Levin 37.3 Manner of Speaking verbs. -/
def shout : Verb where
  morphs := [.root "shout"]
  levin := some Levin1993.Index.shout
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "cry" — Levin 37.3 Manner of Speaking verbs. -/
def cry : Verb where
  morphs := [.root "cry"]
  levin := some Levin1993.Index.cry
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "scream" — Levin 37.3 Manner of Speaking verbs. -/
def scream : Verb where
  morphs := [.root "scream"]
  levin := some Levin1993.Index.scream
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "mumble" — Levin 37.3 Manner of Speaking verbs. -/
def mumble : Verb where
  morphs := [.root "mumble"]
  levin := some Levin1993.Index.mumble
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "mutter" — Levin 37.3 Manner of Speaking verbs. -/
def mutter : Verb where
  morphs := [.root "mutter"]
  levin := some Levin1993.Index.mutter
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "shriek" — Levin 37.3 Manner of Speaking verbs. -/
def shriek : Verb where
  morphs := [.root "shriek"]
  levin := some Levin1993.Index.shriek
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "yell" — Levin 37.3 Manner of Speaking verbs. -/
def yell : Verb where
  morphs := [.root "yell"]
  levin := some Levin1993.Index.yell
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "groan" — Levin 37.3 Manner of Speaking verbs. -/
def groan : Verb where
  morphs := [.root "groan"]
  levin := some Levin1993.Index.groan
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "grumble" — Levin 37.3 Manner of Speaking verbs. -/
def grumble : Verb where
  morphs := [.root "grumble"]
  levin := some Levin1993.Index.grumble
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "hiss" — Levin 37.3 Manner of Speaking verbs. -/
def hiss : Verb where
  morphs := [.root "hiss"]
  levin := some Levin1993.Index.hiss
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "sigh" — Levin 40.2 Nonverbal Expression verbs. -/
def sigh : Verb where
  morphs := [.root "sigh"]
  levin := some Levin1993.Index.sigh
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "whimper" — Levin 37.3 Manner of Speaking verbs. -/
def whimper : Verb where
  morphs := [.root "whimper"]
  levin := some Levin1993.Index.whimper
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "snap" — Levin 37.3 Manner of Speaking verbs. -/
def snap : Verb where
  morphs := [.root "snap"]
  levin := some Levin1993.Index.snap
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity

/-- "speak" — Levin 37.5 Talk verbs. -/
def speak : Verb where
  morphs := [.root "speak"]
  levin := some Levin1993.Index.speak
  past := "spoke"
  pastPart := "spoken"
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.intransitive
  vendlerClass := some .activity
  passivizable := false

/-- "talk" — Levin 37.5 Talk verbs. -/
def talk : Verb where
  morphs := [.root "talk"]
  levin := some Levin1993.Index.talk
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.intransitive
  vendlerClass := some .activity
  passivizable := false

end English.Verbs
