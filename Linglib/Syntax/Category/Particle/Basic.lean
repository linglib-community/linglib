module

public import Linglib.Syntax.Clause.Basic
public import Linglib.Morphology.Word.Basic
public import Mathlib.Data.Fintype.Basic

/-!
# Particle

This file defines `Particle`, the lexical core of an uninflectable function word in Zwicky's
sense: its form, its position relative to its host, and its distribution over the cells of
`Clause.Distribution`, a sentence type in an embedding context. The distribution records where
the source finds the particle obligatory, optional or excluded, and nothing where the source is
silent; it records distributional felicity, not the licensing mechanism, which is a study's
matter. A particle is licensed in a cell where it is possible, and its sentence-type and
embedding-context profiles are the domain and codomain of that relation, derived and never
stored.

## Main definitions

* `Particle`, `Particle.Position`: the entry and its position class.
* `Particle.Licensed`, `Particle.LicensedIn`, `Particle.LicensedInEmbed`: licensing in a cell
  and its two marginals.
* `Particle.IsSentential`: some cell is recorded.
* `Particle.toWord`: the projection to `Word`.

## References

* [zwicky-1985-clitics]
* [sadock-zwicky-1985]
* [bhatt-dayal-2020]
-/

@[expose] public section

open Morphology (Word)
open Clause (EmbeddingContext SentenceType)

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
  distribution : Clause.Distribution := fun _ _ ↦ none
  deriving DecidableEq

namespace Particle

variable (p : Particle) (c : SentenceType) (e : EmbeddingContext)

/-- The particle is positively recorded as available, obligatorily or optionally, in the cell
`(c, e)`. -/
def Licensed : Prop := (c, e) ∈ p.distribution.possible

instance : Decidable (p.Licensed c e) := inferInstanceAs (Decidable (_ ∈ _))

/-- Positively recorded in sentence type `c` in some embedding context. -/
def LicensedIn : Prop := c ∈ p.distribution.possible.dom

instance : Decidable (p.LicensedIn c) := inferInstanceAs (Decidable (_ ∈ _))

/-- Positively recorded in embedding context `e` for some sentence type. -/
def LicensedInEmbed : Prop := e ∈ p.distribution.possible.cod

instance : Decidable (p.LicensedInEmbed e) := inferInstanceAs (Decidable (_ ∈ _))

/-- A particle is sentential when some cell is recorded, as for question, modal and
sentence-final particles. -/
def IsSentential : Prop := p.distribution.recorded.Nonempty

instance : Decidable p.IsSentential := inferInstanceAs (Decidable (Set.Nonempty _))

/-- The projection to `Word`, with the UD tag `PART`. -/
def toWord : Word := { form := p.form, cat := .PART }

end Particle
