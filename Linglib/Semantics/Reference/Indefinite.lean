module

public import Linglib.Core.Order.OrdConnected
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Tactic.DeriveFintype

/-!
# The implicational map of indefinite series

An indefinite series (English *some-*, Russian *-nibud'*) is used in some of nine functions,
which Haspelmath arranges on an implicational map: a graph on the functions whose adjacency
requirement says that the functions a series covers form a connected region. The map is
`implicationalMap`, and a region `s` meets the requirement when
`(implicationalMap.induce ↑s).Connected`, so the book's requirement is a statement of graph
theory. The series themselves are `IndefinitePronoun.Series`.

## Main declarations

* `Indefinite.HaspelmathFunction`: the nine functions, with the book's numbering `number`.
* `Indefinite.implicationalMap`: the map as a `SimpleGraph`, from the ten edges `mapEdges` of
  the book's figure. The map carries nothing beyond the regions it admits
  (`adj_iff_connected_pair`).
* `Indefinite.SpecificityFunction`: the specific known, specific unknown and non-specific
  functions in the order the map chains them, with their embedding `toFunction` in the map and
  the ones a region covers, `specificityFunctions`. A set of them is an interval unless it has
  the two ends without the middle (`SpecificityFunction.ordConnected_iff`).

## Implementation notes

The empty region is not connected, as `SimpleGraph.Connected` requires a vertex; a series covers
at least one function. The book counts the possible regions of the map differently from the
graph encoded here; see the TODO of `Studies/Haspelmath1997.lean`.

## References

* [haspelmath-1997]
* [farkas-brasoveanu-2020]
-/

@[expose] public section

namespace Indefinite

/-! ### The functions and the map -/

/-- The nine functions of [haspelmath-1997]'s implicational map. -/
inductive HaspelmathFunction where
  /-- In the specific known function the speaker has a referent in mind. -/
  | specificKnown
  /-- In the specific unknown function the speaker presupposes a referent but cannot identify
  it. -/
  | specificUnknown
  /-- In the irrealis non-specific function no specific referent is intended. -/
  | irrealis
  /-- The indefinite stands in a question. -/
  | question
  /-- The indefinite stands in the protasis of a conditional. -/
  | conditional
  /-- The indefinite stands in the standard of a comparative. -/
  | comparative
  /-- Indirect negation is superordinate or implicit negation (*without*, *doubt*, *deny*). -/
  | indirectNeg
  /-- Direct negation is clause-mate negation. -/
  | directNeg
  /-- The indefinite is a free-choice item. -/
  | freeChoice
  deriving DecidableEq, Fintype, Repr

namespace HaspelmathFunction

/-- The book's numbering of the functions, in which it states the distribution of a series. -/
def number : HaspelmathFunction → ℕ
  | .specificKnown => 1
  | .specificUnknown => 2
  | .irrealis => 3
  | .question => 4
  | .conditional => 5
  | .indirectNeg => 6
  | .directNeg => 7
  | .comparative => 8
  | .freeChoice => 9

theorem number_injective : Function.Injective number := by decide

end HaspelmathFunction

/-- The ten edges of the implicational map, the lines of [haspelmath-1997]'s figure, each stated
once as an unordered pair. -/
def mapEdges : Finset (Sym2 HaspelmathFunction) :=
  {s(.specificKnown, .specificUnknown), s(.specificUnknown, .irrealis),
    s(.irrealis, .question), s(.irrealis, .conditional), s(.question, .conditional),
    s(.question, .indirectNeg), s(.conditional, .comparative), s(.indirectNeg, .directNeg),
    s(.indirectNeg, .comparative), s(.comparative, .freeChoice)}

/-- The implicational map is the graph on the functions whose edges are `mapEdges`: a chain from
specific known through specific unknown to irrealis, which feeds two parallel tracks, question to
indirect negation to direct negation and conditional to comparative to free choice, the tracks
joined at question and conditional and at indirect negation and comparative.

```
                      (4) question —— (6) indirect neg —— (7) direct neg
                           |                |
(1) SK — (2) SU — (3) irr <
                           |                |
                      (5) conditional — (8) comparative — (9) free choice
```
-/
def implicationalMap : SimpleGraph HaspelmathFunction :=
  .fromEdgeSet ↑mapEdges

instance : DecidableRel implicationalMap.Adj := fun f g ↦
  inferInstanceAs (Decidable (s(f, g) ∈ (↑mapEdges : Set (Sym2 HaspelmathFunction)) ∧ f ≠ g))

@[simp]
theorem implicationalMap_adj {f g : HaspelmathFunction} :
    implicationalMap.Adj f g ↔ s(f, g) ∈ mapEdges ∧ f ≠ g := by
  rw [implicationalMap, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe]

/-- The ten pairs of `mapEdges` are exactly the map's edges: none is a loop and none repeats. -/
theorem edgeFinset_implicationalMap : implicationalMap.edgeFinset = mapEdges := by
  decide

/-- The map carries nothing beyond the regions it admits: two functions are adjacent exactly
when the pair of them is a connected region, so the graph and its family of regions determine
each other. -/
theorem adj_iff_connected_pair {f g : HaspelmathFunction} :
    implicationalMap.Adj f g ↔ f ≠ g ∧ (implicationalMap.induce {f, g}).Connected := by
  simp only [SimpleGraph.connected_iff_exists_forall_reachable]
  revert f g
  decide +kernel

/-! ### The specificity functions -/

/-- The three functions at the specific end of the map, which differ in whether the indefinite
has a specific referent and in whether the speaker can identify it. They are ordered as the map
chains them, from specific known through specific unknown to non-specific. The two specific
functions differ in epistemic specificity ([farkas-brasoveanu-2020]), whether the referent is
fixed across what the speaker believes. -/
inductive SpecificityFunction where
  /-- The speaker has the referent in mind. -/
  | specificKnown
  /-- The speaker presupposes a referent but cannot identify it. -/
  | specificUnknown
  /-- No specific referent is intended. -/
  | nonSpecific
  deriving DecidableEq, Fintype, Repr

namespace SpecificityFunction

instance : LinearOrder SpecificityFunction :=
  LinearOrder.lift' SpecificityFunction.ctorIdx (by decide)

instance : LocallyFiniteOrder SpecificityFunction := Fintype.toLocallyFiniteOrder

/-- A set of specificity functions is an interval exactly when it does not have the two ends
without the middle. -/
theorem ordConnected_iff {s : Set SpecificityFunction} :
    s.OrdConnected ↔ (specificKnown ∈ s → nonSpecific ∈ s → specificUnknown ∈ s) := by
  refine ⟨fun h hk hn ↦ h.out hk hn ⟨by decide, by decide⟩, fun h ↦ ⟨?_⟩⟩
  rintro (_ | _ | _) ha (_ | _ | _) hb (_ | _ | _) ⟨hac, hcb⟩ <;>
    first
      | assumption
      | exact h ha hb
      | exact absurd hac (by decide)
      | exact absurd hcb (by decide)

/-- `toFunction` embeds the specificity functions in the map, the non-specific function as the
irrealis one. -/
def toFunction : SpecificityFunction → HaspelmathFunction
  | .specificKnown => .specificKnown
  | .specificUnknown => .specificUnknown
  | .nonSpecific => .irrealis

theorem toFunction_injective : Function.Injective toFunction := by decide

/-- `toFunction` embeds the chain in the map as an induced path: two specificity functions are
adjacent on the map exactly when they are neighbours in the chain. -/
theorem adj_toFunction_iff {u v : SpecificityFunction} :
    implicationalMap.Adj u.toFunction v.toFunction ↔
      (SimpleGraph.hasse SpecificityFunction).Adj u v := by
  revert u v; decide

end SpecificityFunction

/-- The specificity functions a region of the map covers. -/
def specificityFunctions (s : Finset HaspelmathFunction) : Finset SpecificityFunction :=
  Finset.univ.filter (·.toFunction ∈ s)

@[simp]
theorem mem_specificityFunctions {s : Finset HaspelmathFunction} {u : SpecificityFunction} :
    u ∈ specificityFunctions s ↔ u.toFunction ∈ s := by
  simp [specificityFunctions]

end Indefinite
