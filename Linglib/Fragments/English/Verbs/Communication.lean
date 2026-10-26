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

open ArgumentStructure Aspect Degree

/-! ### Communication -/

/-- "say" — communication verb, not factive -/
def say : Verb where
  morphs := [.root "say"]
  past := "said"
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.say}

/-- "tell" — communication verb with recipient.
    Also ditransitive ("tell me a story"). The direct object may be implicit in the double
    object frame only, a definite (*Tell me*, but not *told to me*); the PP may be implicit, an
    indefinite ([bruening-2021]). -/
def tell : Verb where
  morphs := [.root "tell"]
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
  levinClasses := {LevinClass.tell, .transferOfMessage}

/-- "claim" — communication verb, speaker doesn't endorse -/
def claim : Verb where
  morphs := [.root "claim"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .achievement
  levinClasses := {LevinClass.say}

/-! ### Manner of Speaking (Levin 37.3)

Manner-of-speaking verbs specify how something is said. -/

/-- "whisper" — Levin 37.3 Manner of Speaking verbs. -/
def whisper : Verb where
  morphs := [.root "whisper"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking}

/-- "murmur" — Levin 37.3 Manner of Speaking verbs. -/
def murmur : Verb where
  morphs := [.root "murmur"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission}

/-- "shout" — Levin 37.3 Manner of Speaking verbs. -/
def shout : Verb where
  morphs := [.root "shout"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking}

/-- "cry" — Levin 37.3 Manner of Speaking verbs. -/
def cry : Verb where
  morphs := [.root "cry"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.breathe, .mannerOfSpeaking, .marvel, .nonverbalExpression,
    .soundEmission}

/-- "scream" — Levin 37.3 Manner of Speaking verbs. -/
def scream : Verb where
  morphs := [.root "scream"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking, .soundEmission}

/-- "mumble" — Levin 37.3 Manner of Speaking verbs. -/
def mumble : Verb where
  morphs := [.root "mumble"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking}

/-- "mutter" — Levin 37.3 Manner of Speaking verbs. -/
def mutter : Verb where
  morphs := [.root "mutter"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking}

/-- "shriek" — Levin 37.3 Manner of Speaking verbs. -/
def shriek : Verb where
  morphs := [.root "shriek"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .soundEmission}

/-- "yell" — Levin 37.3 Manner of Speaking verbs. -/
def yell : Verb where
  morphs := [.root "yell"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking}

/-- "groan" — Levin 37.3 Manner of Speaking verbs. -/
def groan : Verb where
  morphs := [.root "groan"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.mannerOfSpeaking, .nonverbalExpression, .soundEmission}

/-- "grumble" — Levin 37.3 Manner of Speaking verbs. -/
def grumble : Verb where
  morphs := [.root "grumble"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.complain, .mannerOfSpeaking}

/-- "hiss" — Levin 37.3 Manner of Speaking verbs. -/
def hiss : Verb where
  morphs := [.root "hiss"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking, .soundEmission}

/-- "sigh" — Levin 40.2 Nonverbal Expression verbs. -/
def sigh : Verb where
  morphs := [.root "sigh"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.nonverbalExpression}

/-- "whimper" — Levin 37.3 Manner of Speaking verbs. -/
def whimper : Verb where
  morphs := [.root "whimper"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .mannerOfSpeaking}

/-- "snap" — Levin 37.3 Manner of Speaking verbs. -/
def snap : Verb where
  morphs := [.root "snap"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.finiteClause
  vendlerClass := some .activity
  levinClasses := {LevinClass.animalSound, .break_, .crane, .mannerOfSpeaking, .soundEmission}

/-- "speak" — Levin 37.5 Talk verbs. -/
def speak : Verb where
  morphs := [.root "speak"]
  past := "spoke"
  pastPart := "spoken"
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.intransitive
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.talk}

/-- "talk" — Levin 37.5 Talk verbs. -/
def talk : Verb where
  morphs := [.root "talk"]
  speechActVerb := true
  valency := .ofFrame ArgumentFrame.intransitive
  vendlerClass := some .activity
  passivizable := false
  levinClasses := {LevinClass.talk}

end English.Verbs
