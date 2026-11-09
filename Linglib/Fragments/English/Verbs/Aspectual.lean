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

open ArgumentStructure Aspect Data.VerbClasses

/-! ### Change of State -/

/-- "stop" — phasal cessation, presupposes activity was happening -/
def stop : Verb where
  morphs := [.root "stop"]
  levin := some Levin1993.Index.stop
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .cessation

/-- "quit" — phasal cessation -/
def quit : Verb where
  morphs := [.root "quit"]
  levin := some Levin1993.Index.quit
  past := "quit"
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .cessation

/-- "start" — phasal inception, presupposes activity wasn't happening -/
def start : Verb where
  morphs := [.root "start"]
  levin := some Levin1993.Index.start
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .inception

/-- "begin" — phasal inception, raising into its subject before an infinitive (*the bridge began to
tremble*). -/
def begin_ : Verb where
  morphs := [.root "begin"]
  levin := some Levin1993.Index.begin
  past := "began"
  pastPart := "begun"
  doubling := true
  valency := .ofLinks
    [(ArgumentFrame.gerund, [some 0, some 1]),
     (ArgumentFrame.np, [some 0, some 1]),
     (ArgumentFrame.intransitive, [some 1]),
     (toInfinitive, [none, some 1])]
    (controls := [some .external, none, none, some .external])
  vendlerClass := some .achievement
  passivizable := false
  phasal := some .inception

/-- "continue" — phasal continuation, presupposes activity was happening -/
def continue_ : Verb where
  morphs := [.root "continue"]
  levin := some Levin1993.Index.«continue»
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .activity
  passivizable := false
  phasal := some .continuation

/-- "keep" — phasal continuation -/
def keep : Verb where
  morphs := [.root "keep"]
  levin := some Levin1993.Index.keep
  past := "kept"
  valency := .of
    [(ArgumentFrame.gerund, [0, 1]),
     (ArgumentFrame.np, [0, 1]),
     (ArgumentFrame.intransitive, [1])]
    (controllers := [some 0])
  vendlerClass := some .activity
  passivizable := false
  phasal := some .continuation

end English.Verbs
