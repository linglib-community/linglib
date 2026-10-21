module

public import Linglib.Morphology.Morph
public import Mathlib.Tactic.DeriveFintype

/-!
# The form of negation

This file records how a language expresses sentential negation: the marker that expresses it and
where the marker sits. What negation means is the negative polarity, which acts on a proposition
by complement (`Polarity.negative`), and the strengths of negation a context can carry are
`Negation.Strength`, both in `Semantics/Polarity`.

A language negates a declarative verbal main clause with a marker: an affix on the verb, a free
particle, an inflecting negative verb, or two morphemes at once (French *ne … pas*). A negative
may differ from its affirmative only by the marker, or the clause may also change, taking a
nonfinite verb form or losing tense distinctions, the divide Miestamo calls symmetric and
asymmetric. In a negative polar interrogative the negation is preposed with the finite verb, as
English *n't* in *Isn't Jane coming?*, or not, as *not* in *Is Jane not coming?*, the distinction
Romero and Han draw.

## Main definitions

* `Negation.Marker`: a standard negation marker, as the morphs exponing it.
* `Negation.Position`: preposed or non-preposed negation.

## Implementation notes

* A typology of markers or of negative constructions is one author's classification and lives in
  that author's study, such as Miestamo's symmetry in `Studies/Miestamo2005.lean`, whose
  affirmative–negative pairs are its example rows. An inflecting negative verb is cited by its
  stem, and its endings form an `Agreement.Paradigm` in the language's fragment.
* The form of a polar interrogative is an `Option Negation.Position`, `none` for a positive
  question, which gives Romero's PosQ, LoNQ and HiNQ. Forms and readings are related, not
  identified: the preposed *-n't* of *Isn't this the road to Lund?* has both readings for some
  speakers of English, so each language or variety relates a form to a set of readings.
* Structural positions of negation are a framework's, such as the heights relative to the
  polarity head in `Minimalist.ClauseNegation`.

## References

* [miestamo-2005]
* [romero-han-2004]
* [romero-2024]
-/

@[expose] public section

namespace Negation

open Morphology (Morph)

/-- A standard sentential negation marker. -/
structure Marker where
  /-- The exponent as contiguous pieces in surface order; a bipartite
      marker has two (Burmese *ma-…-bu*). Affixal alternants are recorded by
      an abstract citation form (Turkish *-mA-* for *-ma-* ~ *-me-*). -/
  pieces : List (List Morph)
  deriving DecidableEq, Repr

/-- The surface form of a marker is its pieces in boundary notation, separated by `…`. -/
def Marker.form (m : Marker) : String := String.intercalate "…" (m.pieces.map Morph.surface)

/-- The morphs of a marker, across its pieces. -/
def Marker.morphs (m : Marker) : List Morph := m.pieces.flatten

/-- The position of the negation of a negative polar interrogative relative to the rest of the
clause, preposed with the finite verb or in its clause-internal position. What matters is the
relative position, not a particular one. -/
inductive Position where
  /-- Negation preposed with the finite verb. -/
  | preposed
  /-- Negation in its clause-internal position. -/
  | nonPreposed
  deriving DecidableEq, Repr, Fintype

end Negation
