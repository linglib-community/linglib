/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.DistributedMorphology.Basic
public import Linglib.Morphology.Word.Tree

/-!
# The word tree of a complex head

The word tree of a complex head attaches each head on the side its exponent takes, innermost
first. On each side, its surface order outward from the root is then the order in which the heads
were merged.

## Main definitions

* `DistributedMorphology.ComplexHead.toTree`: the word tree of a complex head.
* `DistributedMorphology.ComplexHead.surface`: the surface order of its root and heads.

## Main results

* `DistributedMorphology.ComplexHead.surface_eq`: the surface is the prefixal heads outermost
  first, the root, and the suffixal heads innermost first.

## TODO

* A complex head is one root with a chain of heads, so a compound and a head with no root cannot
  be stated, and the order of the tree holds by the definition of `toTree`. Decide whether the
  shared type should be the more general `MorphosyntacticWord`.

## References

* [halle-marantz-1993]
* [baker-1985]
-/

@[expose] public section

namespace DistributedMorphology

open Morphology (Morph)

namespace ComplexHead

variable {R H : Type*} (s : ComplexHead R H)

/-- The word tree, each head attached on the side its exponent takes, innermost first. -/
def toTree (side : H → Morph.Side) : Morphology.Word.Tree (R ⊕ H) :=
  Morphology.Word.Tree.attachAll (.inl s.root) (s.heads.map fun h => (side h, .inr h))

/-- The surface order of root and heads. -/
def surface (side : H → Morph.Side) : List (R ⊕ H) := (s.toTree side).toList

/-- **The Mirror Principle.** The surface is the prefixal heads outermost first, the root, and the
suffixal heads innermost first, so on each side the surface order outward from the root is the
order of merger. -/
theorem surface_eq (side : H → Morph.Side) :
    s.surface side =
      ((s.heads.filter fun h => side h = .before).map Sum.inr).reverse ++
        Sum.inl s.root :: (s.heads.filter fun h => side h = .after).map Sum.inr := by
  simp [surface, toTree, Morphology.Word.Tree.toList_attachAll, List.filter_map, List.map_map,
    Function.comp_def]

end ComplexHead

end DistributedMorphology
