module

public import Linglib.Syntax.Clause.Basic

/-!
# Particles

A particle is an uninflected function word associated with a host: a clause, as a question particle
is, or a constituent, as a focus particle is. This file defines its lexical record, which gives the
form, the position relative to the host, and a `Clause.Distribution` saying, for each sentence type
in each embedding context, whether the particle is obligatory, optional or excluded there. The
cells where a particle `p` may occur are `p.distribution.possible`, and the sentence types and
embedding contexts that admit it are the `dom` and `cod` of that relation.

## Main definitions

* `Particle.Position`: the position classes, relative to the clause or to a host constituent.
* `Particle`: the form, position and distribution of a particle.

## Implementation notes

* The form is a string, so the record does not say whether a particle is a word or a clitic.
  `Coordinator` and `AdditiveParticle` record a `Morphology.Morph`, which does.
* A distribution says where a particle occurs and not what licenses it there. A cell on which the
  source is silent is `none`, and so is a position the source does not give; a particle with no
  fixed position has `Particle.Position.free`.

## TODO

* Record the form as morphs, as `Complementizer` does, so that an enclitic such as Russian *li*
  and a free word such as *razve* differ in kind and not only in position.

## References

* [zwicky-1985-clitics]
* [sadock-zwicky-1985]
* [bhatt-dayal-2020]
-/

@[expose] public section

/-- Where a particle stands, in its clause or beside a host constituent. -/
inductive Particle.Position where
  | clauseInitial
  /-- Second position (Wackernagel; Russian *li*). -/
  | secondPosition
  /-- Clause-medial / middle field (German *denn*, Swedish *väl*). -/
  | clauseMedial
  | clauseFinal
  /-- Immediately before a host constituent (adnominal focus particles). -/
  | preHost
  /-- Immediately after a host constituent (Turkish *mI*, Bulgarian *li* on the focus). -/
  | postHost
  /-- No fixed position (Hindi-Urdu *kya:*). -/
  | free
  deriving DecidableEq, Repr, Fintype

/-- An uninflectable function word associated with a host constituent. -/
structure Particle where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Native-script form, when `form` is a romanization (Mandarin 吗). -/
  script : Option String := none
  /-- Host/position class; `none` when the source records no placement. -/
  position : Option Particle.Position := none
  /-- How far the particle is required in each cell; `none` where the source records
      nothing. -/
  distribution : Clause.Distribution := .empty
  deriving DecidableEq
