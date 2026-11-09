module

public import Mathlib.Logic.Function.Basic

/-!
# Many-sorted algebraic languages and structures

A many-sorted language has function symbols typed by the sorts of their arguments and the sort of
their result, where a first-order language of mathlib has symbols of each arity. The arguments of
a symbol have a shape, a `Signature`: none, one of a sort, or a pair of shapes, and a structure
gives each symbol a function from the product of domains that its shape describes.

## Main definitions

* `MSFirstOrder.Signature`: the shape of a symbol's arguments.
* `MSFirstOrder.Signature.Interpret`: the arguments of a shape, over a family of domains.
* `MSFirstOrder.Language`: function symbols by argument shape and result sort.
* `MSFirstOrder.Language.Structure`: a function for each symbol, over a family of domains.

## Implementation notes

The definitions follow the many-sorted generalization of `FirstOrder.Language` being developed
outside mathlib, in which a shape is a binary tree of sorts read as a nested product, so that a
binary symbol takes a pair. Only function symbols are defined: a language here is what that
development calls algebraic. The domains are a parameter of a structure.
-/

@[expose] public section

universe u v w

namespace MSFirstOrder

/-- The shape of a symbol's arguments over sorts `S`: none, one of a sort, or a pair of shapes. -/
inductive Signature (S : Type u) where
  /-- No arguments. -/
  | nil : Signature S
  /-- One argument of a sort. -/
  | of (s : S) : Signature S
  /-- The arguments of one shape paired with those of another. -/
  | prod (σ τ : Signature S) : Signature S

variable {S : Type u}

/-- The arguments of a shape over the domains `X`: a nested product. -/
abbrev Signature.Interpret (X : S → Type w) : Signature S → Type w
  | .nil => PUnit
  | .of s => X s
  | .prod σ τ => Interpret X σ × Interpret X τ

/-- A many-sorted algebraic language over sorts `S`: the function symbols with arguments of a
given shape and a result of a given sort. -/
structure Language (S : Type u) where
  /-- The function symbols with arguments of shape `σ` and result of sort `t`. -/
  Functions : Signature S → S → Type v

/-- A structure for a language over the domains `D`: a function for each symbol. -/
structure Language.Structure (L : Language.{u, v} S) (D : S → Type w) where
  /-- The function a symbol denotes. -/
  funMap {σ : Signature S} {t : S} : L.Functions σ t → σ.Interpret D → D t

end MSFirstOrder
