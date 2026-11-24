/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Data.WALS.Features.F121A
public import Linglib.Syntax.Feature.Case.Basic
public import Linglib.Morphology.Morph

/-!
# Comparative constructions

A comparative construction, *X is taller than Y*, marks the standard of comparison *Y* and may
mark the degree on the predicate. Stassen classifies constructions by the encoding of the
standard: its case is derived from the case of the comparee, or it is fixed by the construction,
and a standard in a fixed case is the direct object of a verb of exceeding or part of an adverbial
phrase. We define a construction by the encoding of its standard, `Comparative.Standard`, and by
its markers, and derive from them its type in Stassen's chapter of the World Atlas of Language
Structures.

## Main definitions

* `Comparative.Standard`: the encoding of the standard of comparison.
* `Comparative`: a construction, with the marker of its standard and its markers of degree as
  morphs.
* `Comparative.type`: the type of a construction in the atlas.

## Implementation notes

The encoding of the standard is one inductive type and not a field for each of Stassen's
parameters, since the parameters are nested: only a standard in a fixed case is a direct object
or an adverbial, and only an adverbial standard has a case of its own.

## References

* [stassen-1985]
* [stassen-2013]
* [wals-2013]
-/

@[expose] public section

/-- The encoding of the standard of comparison in the parameters of [stassen-1985]. -/
inductive Comparative.Standard where
  /-- The standard takes its case from the comparee, as after Latin *quam*. -/
  | derived
  /-- The standard is the direct object of a transitive verb of exceeding. -/
  | directObject
  /-- The standard is part of an adverbial phrase, in the case given where the phrase has one,
  the ablative of a separative and the partitive of the Finnish secondary construction. An
  adposition with the meaning of the case counts, as Japanese *yori* and Arabic *min* do for the
  ablative. -/
  | adverbial (case : Option Case)
  deriving DecidableEq, Repr

/-- The case of an adverbial standard. -/
def Comparative.Standard.case? : Comparative.Standard → Option Case
  | adverbial k => k
  | _ => none

/-- A comparative construction, by the way it encodes the standard of comparison in *X is more
Adj than Y*. A language may have more than one, as Latin has *quam* and the bare ablative. -/
structure Comparative where
  /-- The marker of the standard as the morphs of its form in order, *than* or the two pieces
  of Yoruba *ju … lọ*. It is empty where no segmental marker flags the standard, as in a
  conjoined construction and with a bare case-marked standard like the Latin ablative. -/
  standardMarker : List Morphology.Morph := []
  /-- The encoding of the standard. -/
  standard : Comparative.Standard
  /-- The markers of degree on the predicate, each an alternative, as English *more* and *-er*.
  A bound marker is degree morphology and a free one a degree word, and the list is empty where
  the construction marks no degree. -/
  degreeMarkers : List Morphology.Morph := []
  deriving Repr, BEq, DecidableEq

namespace Comparative

/-! ### The derived type -/

/-- The type of a construction in the atlas. A construction with a standard in a derived case is
a particle comparative when it has a standard marker, as English *than* and German *als*, and a
conjoined one otherwise, two juxtaposed clauses that attribute the property to one item and deny
it of the other or contrast them. A construction is an exceed comparative when the standard is a
direct object, as of the exceed verb in Yoruba *X Adj ju Y lọ*, and a locational one when the
standard is adverbial, as Japanese *yori*, Turkish *-DAn* and Hindi-Urdu *se*. -/
def type (c : Comparative) : Data.WALS.F121A.ComparativeType :=
  match c.standard with
  | .derived => if c.standardMarker = [] then .conjoined else .particle
  | .directObject => .exceed
  | .adverbial _ => .locational

end Comparative
