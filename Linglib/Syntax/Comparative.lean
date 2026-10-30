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
World Atlas of Language Structures. The types are the values of the atlas's feature
(`ComparativeType.toWALS` is a bijection), and through them the file counts the atlas's sample:
the locational type is the most common and the particle type the rarest.

## Main definitions

* `Comparative`: a construction, with the marker of its standard and its markers of degree as
  morphs.
* `Comparative.type`: the type of a construction in the atlas.
* `Comparative.ComparativeType.toWALS`: the value of the atlas's feature that a type is.
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

abbrev ch121 := Data.WALS.F121A.allData

/-! ### Classifications -/

/-- The type of a comparative construction in the atlas, by how it encodes the standard of
comparison. A language with more than one productive construction has one `Comparative` for
each, with its own type. -/
inductive ComparativeType where
  /-- The standard is marked with a locational or ablative case or adposition, as in Japanese
  *Y yori X tall*, Turkish, Hindi-Urdu and the Latin ablative. -/
  | locational
  /-- A verb meaning 'exceed' or 'surpass' encodes the comparison, as in Yoruba
  *Ade ga ju Bola lo*. -/
  | exceed
  /-- Two juxtaposed clauses, one attributing the property to X and the other denying it of Y
  or contrasting it. -/
  | conjoined
  /-- A dedicated comparative particle marks the standard, as English *than* and German *als*
  do. -/
  | particle
  deriving DecidableEq, BEq, Repr

/-- The value of the atlas's feature 121A that a type is. -/
def ComparativeType.toWALS : ComparativeType → Data.WALS.F121A.ComparativeType
  | .locational => .locational
  | .exceed => .exceed
  | .conjoined => .conjoined
  | .particle => .particle

theorem ComparativeType.toWALS_bijective : Function.Bijective ComparativeType.toWALS := by
  refine ⟨fun a b h ↦ ?_, fun y ↦ ?_⟩
  · cases a <;> cases b <;> first | rfl | cases h
  · cases y
    exacts [⟨.locational, rfl⟩, ⟨.exceed, rfl⟩, ⟨.conjoined, rfl⟩, ⟨.particle, rfl⟩]

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
construction is a particle comparative when it has a standard marker and a conjoined one
otherwise, and a fixed-case construction is an exceed comparative when the standard is a direct
object and a locational one otherwise. -/
def type (c : Comparative) : ComparativeType :=
  match c.caseAssignment, c.fixedEncoding with
  | .derived, _ => if c.standardMarker = [] then .conjoined else .particle
  | .fixed, some .directObject => .exceed
  | .fixed, _ => .locational

/-! ### Counts over the sample of the atlas -/

theorem locational_most_common (t : ComparativeType) (ht : t ≠ .locational) :
    (ch121.filter (·.2 = t.toWALS)).length <
      (ch121.filter (·.2 = ComparativeType.locational.toWALS)).length := by
  cases t <;> first | exact absurd rfl ht | decide +kernel

theorem particle_rarest (t : ComparativeType) (ht : t ≠ .particle) :
    (ch121.filter (·.2 = ComparativeType.particle.toWALS)).length <
      (ch121.filter (·.2 = t.toWALS)).length := by
  cases t <;> first | exact absurd rfl ht | decide +kernel

theorem locational_and_particle_dominant :
    ch121.length / 2 < (ch121.filter (·.2 = ComparativeType.locational.toWALS)).length +
      (ch121.filter (·.2 = ComparativeType.particle.toWALS)).length := by
  decide +kernel

end Comparative
