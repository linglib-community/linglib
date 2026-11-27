/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Tactic.DeriveFintype

/-!
# Focus particles and markers

This file defines the lexical record of a particle that goes with a focused or associated
constituent, as the Yorùbá focus marker *ni* and exclusive *nìkan* do: its form and its position
relative to that constituent or in the clause. A particle that goes with a clause as a whole is a
`Clause.Marker`.

## Main definitions

* `Particle.Position`: the position classes, relative to the clause or to a host constituent.
* `Particle`: the form and position of a particle.

## TODO

* Record an exclusive or additive particle with the focus operator it denotes, as
  `AdditiveParticle` does, and a focus marker with the focus strategy it realizes.

## References

* [zwicky-1985-clitics]
-/

@[expose] public section

/-- Where a particle stands, in its clause or beside a host constituent. -/
inductive Particle.Position where
  | clauseInitial
  /-- Second position. -/
  | secondPosition
  /-- Clause-medial, as Yorùbá *kàn* between the subject and the verb. -/
  | clauseMedial
  | clauseFinal
  /-- Immediately before a host constituent. -/
  | preHost
  /-- Immediately after a host constituent, as Yorùbá *ni* after the fronted focus. -/
  | postHost
  /-- No fixed position. -/
  | free
  deriving DecidableEq, Repr, Fintype

/-- A particle associated with a host constituent. -/
structure Particle where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Native-script form, when `form` is a romanization. -/
  script : Option String := none
  /-- Host/position class; `none` when the source records no placement. -/
  position : Option Particle.Position := none
  deriving DecidableEq
