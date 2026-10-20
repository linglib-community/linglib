module

public import Linglib.Data.UD.UPOS
public import Linglib.Data.UD.Features
public import Linglib.Syntax.Clause.Basic
public import Linglib.Syntax.Clause.Complementation
public import Linglib.Morphology.Morph
public import Linglib.Morphology.Word.Basic

/-!
# Complementizer

The lexical core of the complementizer (clause-typing morpheme) as a
grammatical object, modeled on `Syntax/Category/Pronoun/`: its exponent
as morphs plus the consensus clause-typing axes, each drawn from
existing substrate. Per-language fragments instantiate it — free
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

- `morphs` lists the exponent in surface order: a free word (*that*), a
  bound root that never surfaces bare (Buryat *gɘ*), or the
  affixes of a prefix or suffix complex (Tigrinya *kɛm-zɨ-*). Attachment
  is read off the morphs' kinds rather than stored.
- `types`: the sentence types of the clauses the morpheme types, a
  selection; a complementizer of polar questions records `.only .polar`.
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

/-- A complementizer is its exponent as morphs together with the consensus clause-typing
axes. -/
structure Complementizer where
  /-- The exponent, in surface order. -/
  morphs : List Morph
  /-- [noonan-2007] coding of the clause this morpheme types. -/
  coding : Option Clause.ComplementType := none
  /-- The sentence types of the clauses this morpheme types. -/
  types : Clause.Selection := ⊥
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

/-- A complementizer is finite when its verb form or its coding is finite. -/
def IsFinite (c : Complementizer) : Prop := c.verbForm = some .Fin ∨ ∃ k ∈ c.coding, k.IsFinite

instance : DecidablePred IsFinite := fun c ↦
  inferInstanceAs (Decidable (_ ∨ ∃ k ∈ c.coding, _))

end Complementizer
