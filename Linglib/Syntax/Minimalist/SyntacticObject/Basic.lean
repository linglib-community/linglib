/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.FreeCommMagma

/-!
# Syntactic objects

[marcolli-chomsky-berwick-2025] define the syntactic objects as the free nonassociative
commutative magma on the lexical items, with Merge as its product, and the planar syntactic
objects as the free magma on the same items. Here `SyntacticObject α` and
`PlanarSyntacticObject α` are those two magmas on any leaves `α`, and
[forgetting the order of daughters](##Minimalist.PlanarSyntacticObject.toSyntacticObject) is the
projection between them. A map of leaves relabels them, injectively when it is injective. The
trees of the two kinds of object are in `SyntacticObject/Tree.lean`.

## Implementation notes

* The leaves are a parameter with no default, so this file does not import the lexicon. The
  objects of a derivation are on `Minimalist.TokenLeaf` of `SyntacticObject/Token.lean`, the
  tokens of lexical items; a file that names it is about lexical items, and a file that does not
  is about any leaves.
* The two types are abbreviations, so the API of `FreeMagma` and `FreeCommMagma` applies to them
  directly: `*` is Merge, and a map out of either is determined by its values on the leaves.
* No leaf is a trace. A term that has moved occurs at each place it has been, and its
  occurrences are the copies of `SyntacticObject/Position.lean`.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

/-- The planar syntactic objects on the leaves `α`, the free magma on them:
[marcolli-chomsky-berwick-2025] §1.12's planar syntactic objects. -/
abbrev PlanarSyntacticObject (α : Type) : Type :=
  FreeMagma α

/-- The syntactic objects on the leaves `α`, the free commutative magma on them. -/
abbrev SyntacticObject (α : Type) : Type :=
  FreeCommMagma α

variable {α β γ : Type}

namespace PlanarSyntacticObject

/-- A leaf, the object of one item. -/
abbrev leaf (a : α) : PlanarSyntacticObject α := FreeMagma.of a

/-- Merge, with the daughters in the given order, also written `*`. -/
abbrev merge (l r : PlanarSyntacticObject α) : PlanarSyntacticObject α := l * r

/-- Forgetting the order is the quotient map to the syntactic object. -/
@[coe] def toSyntacticObject (p : PlanarSyntacticObject α) : SyntacticObject α :=
  FreeMagma.toFreeCommMagma p

@[simp] theorem toSyntacticObject_of (a : α) :
    toSyntacticObject (FreeMagma.of a : PlanarSyntacticObject α) = FreeCommMagma.of a := rfl

@[simp] theorem toSyntacticObject_mul (l r : PlanarSyntacticObject α) :
    toSyntacticObject (l * r) = toSyntacticObject l * toSyntacticObject r :=
  map_mul FreeMagma.toFreeCommMagma l r

theorem toSyntacticObject_surjective :
    Function.Surjective (toSyntacticObject : PlanarSyntacticObject α → SyntacticObject α) :=
  FreeMagma.toFreeCommMagma_surjective

end PlanarSyntacticObject

namespace SyntacticObject

/-- A leaf, the object of one item. -/
abbrev leaf (a : α) : SyntacticObject α := FreeCommMagma.of a

/-- Merge on the carrier, the product of the free commutative magma, also written `*`. -/
abbrev merge (l r : SyntacticObject α) : SyntacticObject α := l * r

theorem leaf_injective : Function.Injective (leaf : α → SyntacticObject α) :=
  FreeCommMagma.of_injective

/-- The object with its leaves relabelled by `f`. -/
def map (f : α → β) (s : SyntacticObject α) : SyntacticObject β := FreeCommMagma.map f s

@[simp] theorem map_of (f : α → β) (a : α) :
    map f (FreeCommMagma.of a : SyntacticObject α) = FreeCommMagma.of (f a) := rfl

@[simp] theorem map_merge (f : α → β) (l r : SyntacticObject α) :
    map f (l * r) = map f l * map f r :=
  map_mul (FreeCommMagma.map f) l r

@[simp] theorem map_id (s : SyntacticObject α) : map id s = s := by
  rw [map, FreeCommMagma.map_id]; rfl

@[simp] theorem map_map (f : α → β) (g : β → γ) (s : SyntacticObject α) :
    map g (map f s) = map (g ∘ f) s := by
  rw [map, map, map, FreeCommMagma.map_comp]; rfl

theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (map f : SyntacticObject α → SyntacticObject β) :=
  FreeCommMagma.map_injective hf

end SyntacticObject

end Minimalist
