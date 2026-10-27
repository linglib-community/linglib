module

public import Linglib.Syntax.Clause.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Particle

A `Particle` is the lexical core of an uninflectable function word in Zwicky's sense: its form, its
position relative to its host, and its `Clause.Distribution` over sentence types in embedding
contexts. The distribution records where the source finds the particle obligatory, optional or
excluded, and nothing where the source is silent; it records distributional felicity, not the
licensing mechanism, which is a study's matter. The cells where a particle is licensed are
`p.distribution.possible`, and its sentence-type and embedding-context profiles are that
relation's `dom` and `cod`.

## Main definitions

* `Particle`, `Particle.Position`: the entry and its position class.

## References

* [zwicky-1985-clitics]
* [sadock-zwicky-1985]
* [bhatt-dayal-2020]
-/

@[expose] public section

/-- Where a particle sits relative to its host domain, Zwicky's positional diagnostic. -/
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
  deriving DecidableEq, Repr

/-- An uninflectable function word associated with a host constituent. -/
structure Particle where
  /-- Surface form (romanization or orthographic). -/
  form : String
  /-- Native-script form, when `form` is a romanization (Mandarin 吗). -/
  script : Option String := none
  /-- Host/position class; `none` when the source records no placement. -/
  position : Option Particle.Position := none
  /-- The recorded occurrence of the particle in each cell; `none` where the source records
      nothing. -/
  distribution : Clause.Distribution := .empty
  deriving DecidableEq
