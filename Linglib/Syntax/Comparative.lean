module

public import Linglib.Data.WALS.Features.F121A
public import Linglib.Syntax.Case.Basic
public import Linglib.Morphology.Morph

/-!
# Comparative constructions

A comparative construction, *X is taller than Y*, marks the standard of comparison *Y* and may
mark the degree on the predicate. Stassen classifies constructions by the case of the standard,
which is derived from the case of the comparee or fixed by the construction, and by the role of
a fixed-case standard, the object of a verb of exceeding or an adverbial. This file defines the
construction by these parameters and derives from them its type in Stassen's chapter of the
World Atlas of Language Structures, a value of the atlas's feature.

## Main definitions

* `Comparative`: a construction, with the marker of its standard and its markers of degree as
  morphs.
* `Comparative.type`: the type of a construction in the atlas.
* `Comparative.SuperlativeStrategy`: the ways a language forms superlatives.

## References

* [stassen-1985]
* [stassen-2013]
* [wals-2013]
-/

@[expose] public section

/-- The standard of a comparative takes its case from the comparee or has one case that the
construction fixes ([stassen-1985] §2.2.1). -/
inductive Comparative.CaseAssignment where
  | derived
  | fixed
  deriving DecidableEq, Repr

/-- A fixed-case standard is the direct object of a transitive verb of exceeding or an
adverbial ([stassen-1985] §2.2.2). -/
inductive Comparative.FixedCaseEncoding where
  | directObject
  | adverbial
  deriving DecidableEq, Repr

/-- A comparative construction, by the way it encodes the standard of comparison in *X is more
Adj than Y*, in the parameters of [stassen-1985]. A language may have more than one, as Latin
has *quam* and the bare ablative. -/
structure Comparative where
  /-- The marker of the standard as the morphs of its form in order, *than* or the two pieces
  of Yoruba *ju … lọ*. It is empty where no segmental marker flags the standard, as in a
  conjoined construction and with a bare case-marked standard like the Latin ablative. -/
  standardMarker : List Morphology.Morph := []
  /-- The standard takes its case from the comparee or has a case the construction fixes. -/
  caseAssignment : Comparative.CaseAssignment
  /-- The role of a fixed-case standard, the object of a verb of exceeding or an adverbial. -/
  fixedEncoding : Option Comparative.FixedCaseEncoding := none
  /-- The case of an adverbially encoded standard, the ablative of a separative and the partitive
  of the Finnish secondary construction. An adposition with the meaning of the case counts, as
  Japanese *yori* and Arabic *min* do for the ablative. -/
  standardCase : Option Case := none
  /-- The markers of degree on the predicate, each an alternative, as English *more* and *-er*.
  A bound marker is degree morphology and a free one a degree word, and the list is empty where
  the construction marks no degree. -/
  degreeMarkers : List Morphology.Morph := []
  deriving Repr, BEq, DecidableEq

namespace Comparative

/-! ### Superlatives -/

/-- The ways a language forms superlatives, which are partly independent of its comparative
type. -/
inductive SuperlativeStrategy where
  /-- Dedicated superlative morphology, as English *-est* and Latin *-issimus*. -/
  | morphological
  /-- The definite article with the comparative, as French *le plus grand*. -/
  | definiteComparative
  /-- The elative pattern without a comparison class, as Arabic *ʔafʕal*. -/
  | elative
  /-- A verb of exceeding with a universal quantifier, 'X exceeds all'. -/
  | exceedAll
  /-- The comparative with a universal standard, as Japanese *dare yori mo takai*. -/
  | comparativeUniversal
  /-- No dedicated superlative strategy. -/
  | none
  deriving DecidableEq, BEq, Repr

/-! ### The derived type -/

/-- The type of a construction in the atlas, derived from its anatomy. A derived-case
construction is a particle comparative when it has a standard marker, as English *than* and German
*als*, and a conjoined one otherwise, two juxtaposed clauses that attribute the property to one
item and deny it of the other or contrast them. A fixed-case construction is an exceed comparative
when the standard is a direct object, as of the exceed verb in Yoruba *X Adj ju Y lọ*, and a
locational one otherwise, as when the standard is in a locational or ablative case or adposition,
Japanese *yori*, Turkish *-DAn* and Hindi-Urdu *se*. A language with more than one productive
construction has one `Comparative` for each, with its own type. -/
def type (c : Comparative) : Data.WALS.F121A.ComparativeType :=
  match c.caseAssignment, c.fixedEncoding with
  | .derived, _ => if c.standardMarker = [] then .conjoined else .particle
  | .fixed, some .directObject => .exceed
  | .fixed, _ => .locational

end Comparative
