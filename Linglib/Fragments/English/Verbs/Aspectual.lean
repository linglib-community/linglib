module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English aspectual verbs

This file defines the English aspectual verbs *stop*, *quit*, *start*, *begin*, *continue* and
*keep*, which take a complement denoting the event whose phase they assert and presuppose the
adjacent phase.

## References

* [levin-1993]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Degree

/-! ### Change of State -/

/-- "stop" — phasal cessation, presupposes activity was happening -/
def stop : Verb where
  morphs := [.root "stop"]
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .cessation
  levinClasses := {LevinClass.begin, .lodge}

/-- "quit" — phasal cessation -/
def quit : Verb where
  morphs := [.root "quit"]
  past := "quit"
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .cessation
  levinClasses := {LevinClass.complete}

/-- "start" — phasal inception, presupposes activity wasn't happening -/
def start : Verb where
  morphs := [.root "start"]
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .inception
  levinClasses := {LevinClass.begin}

/-- "begin" — phasal inception -/
def begin_ : Verb where
  morphs := [.root "begin"]
  past := "began"
  pastPart := "begun"
  doubling := true
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .inception
  levinClasses := {LevinClass.begin}

/-- "continue" — phasal continuation, presupposes activity was happening -/
def continue_ : Verb where
  morphs := [.root "continue"]
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .activity
  passivizable := false
  phasal := some .continuation
  levinClasses := {LevinClass.begin}

/-- "keep" — phasal continuation -/
def keep : Verb where
  morphs := [.root "keep"]
  past := "kept"
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .activity
  passivizable := false
  phasal := some .continuation
  levinClasses := {LevinClass.begin, .get, .keep}

end English.Verbs
