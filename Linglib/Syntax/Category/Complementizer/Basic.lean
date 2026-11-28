/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.UD.UPOS
public import Linglib.Data.UD.Features
public import Linglib.Syntax.Clause.Marker
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Morphology.Morph

/-!
# Complementizer

The lexical core of the complementizer (clause-typing morpheme) as a
grammatical object, modeled on `Syntax/Category/Pronoun/`: its exponent
as morphs plus the consensus clause-typing axes, each drawn from
existing substrate. Per-language language files instantiate it — free
subordinators like *that* and *oti*, affixal clause-typers like Buryat
*-žA* and Tigrinya *zɨ-*, grammaticalized say-roots like Buryat *gɘ*.

## Main declarations

* `Complementizer`: the general complementizer object.
* `Complementizer.Licenser`: the adnominal or adverbal licensing category.
* `Complementizer.form`: the surface form with boundary notation.
* `Complementizer.IsFinite`: finiteness of the typed clause, read off the verb form or the
  coding.

## Implementation notes

Framework-specific head assignments (a cartographic Force/Fin split, a
ContP-exponence claim, an [n]-feature) are not fields; they live as
Studies-local projections over these entries, and the schema carries no
denotation (cf. `Adjective`'s deferred degree semantics). Field
conventions:

- A complementizer is a `Clause.Marker`, whose `morphs` list the exponent in
  surface order: a free word (*that*), a bound root that never surfaces bare
  (Buryat *gɘ*), or the affixes of a prefix or suffix complex (Tigrinya
  *kɛm-zɨ-*). Attachment is read off the morphs' kinds rather than stored.
- A complementizer is also a `Clause.Selection`: the complement types, sentence
  types and subject realizations of the clauses it types. A complementizer of
  polar questions has `types := {.polar}`. An entry that records a distribution
  has the sentence types that distribution admits, unless it gives others, and
  every sentence type where the distribution admits none.
- `licenser` names the licensing projection, not the morphological
  host stem (which for a suffixal clause-typer is the verb it
  attaches to).
- `factive` records only a lexical factive presupposition carried by
  the morpheme itself (Greek *pu*); it stays `false` when factivity tracks
  the verb or the construction — derived in Studies, never stored.
-/

@[expose] public section

open Morphology (Morph)

/-- Category of the adjacent projection licensing an affixal
clause-typer: adnominal (Buryat *-Aːša*) vs adverbal (Buryat *-žA*). -/
inductive Complementizer.Licenser where
  | nominal
  | verbal
  deriving DecidableEq, Fintype, Repr

/-- A complementizer is a clause marker together with the selection of the clauses it types and the
consensus clause-typing axes. The subject it requires of its clause is its selection's, as *for*
requires an overt accusative one ([huddleston-pullum-2002] ch. 14 §1.4.1). -/
structure Complementizer extends Clause.Marker, Clause.Selection where
  types := if distribution.types.Nonempty then distribution.types else Finset.univ
  /-- Verb form derived on the host (UD). -/
  verbForm : Option UD.VerbForm := none
  /-- Category of the adjacent licensing projection. -/
  licenser : Option Complementizer.Licenser := none
  /-- The morpheme itself carries a factive presupposition. -/
  factive : Bool := false
  deriving Repr, DecidableEq

namespace Complementizer

/-- The surface form is the morphs' forms with their boundary notation. -/
def form (c : Complementizer) : String := Morph.surface c.morphs

/-- A complementizer is finite when its verb form is finite or every complement type it types
is. -/
def IsFinite (c : Complementizer) : Prop := c.verbForm = some .Fin ∨ ∀ k ∈ c.coding, k.IsFinite

instance : DecidablePred IsFinite := fun c ↦
  inferInstanceAs (Decidable (_ ∨ ∀ k ∈ c.coding, _))

end Complementizer
