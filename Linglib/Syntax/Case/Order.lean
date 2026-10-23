module

public import Linglib.Core.Data.List.Sublist
public import Linglib.Syntax.Case.Basic
/-!
# The containment order on Case

Caha takes the representation of a case to be a stack of nested feature shells, so that each case
on a hierarchy of cases contains the cases before it. The hierarchy here is the list
`containment` of the nominative, accusative, genitive, dative and locative, and one case is below
another when it comes earlier in the list, `[c₁, c₂] <+ containment`. The cases off the list, such
as the ergative, the absolutive and the instrumental, are comparable only to themselves. The order
is a scoped instance (`open scoped Case.Caha`), since a theoretical order is an opt-in commitment
and not an order on the inventory. McFadden's nonnominative cases, those containing the
accusative, are the natural class whose shared feature conditions the stem allomorphy that sets
the nominative apart, and the *ABA syncretism law over the order is the framework-neutral
`IsContiguous`.

The directional containment of spatial cases, Place ⊂ Goal ⊂ Source ⊂ Route, is
`Spatial.Path.Direction`, and the decomposition of spatial cases into localization and direction
is in `Syntax/Case/Spatial.lean`.

## Main definitions

* `Case.containment`: the containment hierarchy.
* The scoped `PartialOrder Case` instance in `Case.Caha`: the containment order.
* `Case.IsNonnominative`: the cases containing the accusative.

## Main results

* `Case.IsNonnominative.mem_containment`: every nonnominative case is on the hierarchy.

## Implementation notes

The list is the start of Blake's hierarchy, nominative, accusative or ergative, genitive, dative,
locative, ablative or instrumental, along its accusative alignment and cut before the ablative and
instrumental, which share a position. McFadden takes Blake's hierarchy as Caha updates it, and
Aitha caps it with the postpositions, which the locative stands for here. Caha's own sequences
differ: his Universal Case sequence is nominative, accusative, genitive, dative, instrumental,
comitative, and his Russian order puts the prepositional between the genitive and the dative.
They are stated in `Studies/Caha2009.lean`.

## References

* [caha-2009]
* [blake-1994]
* [mcfadden-2018]
* [aitha-2026]
-/

@[expose] public section

namespace Case

open List

/-- The containment hierarchy is the nominative, accusative, genitive, dative and locative, each
containing the cases before it. -/
def containment : List Case := [.nom, .acc, .gen, .dat, .loc]

theorem nodup_containment : containment.Nodup := by decide

namespace Caha

/-- In the containment order a case is below another when it comes earlier in `containment`, and
a case off the hierarchy is comparable only to itself. -/
scoped instance : PartialOrder Case :=
  haveI := nodup_containment.isStrictOrder_pair_sublist
  partialOrderOfSO fun c₁ c₂ ↦ [c₁, c₂] <+ containment

scoped instance : DecidableLE Case := fun c₁ c₂ ↦
  inferInstanceAs (Decidable (c₁ = c₂ ∨ [c₁, c₂] <+ containment))

scoped instance : DecidableLT Case := fun c₁ c₂ ↦
  inferInstanceAs (Decidable ([c₁, c₂] <+ containment))

end Caha

open scoped Caha

variable {c : Case}

/-- A case is nonnominative when its representation contains the accusative's, `.acc ≤ c` in the
containment order. -/
def IsNonnominative (c : Case) : Prop := (.acc : Case) ≤ c

instance (c : Case) : Decidable (IsNonnominative c) :=
  inferInstanceAs (Decidable ((.acc : Case) ≤ c))

theorem IsNonnominative.mem_containment (h : IsNonnominative c) : c ∈ containment := by
  rcases h with rfl | h
  · decide
  · exact h.subset (by simp)

end Case
