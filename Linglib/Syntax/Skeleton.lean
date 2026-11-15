module

public import Mathlib.Data.Nat.Notation

/-!
# Bare structures

A bare structure is what a syntactic object hands to interpretation: its terminals in their
constituency and order, with a label at each node. A syntactic theory says what the bare
structure of its objects is, and an interpreter reads meanings off it, so that neither needs
the other's definitions.

## Main definitions

* `Interpreter.Skeleton`: a bare structure over node labels and leaves.
* `Interpreter.Node`: the labels a constituency tree gives its nodes, a plain node, an island,
  or the index of a moved phrase.

## References

* [bumford-charlow-2026]
* [heim-kratzer-1998]
-/

@[expose] public section

universe v w

namespace Interpreter

/-- A bare structure over node labels `N` and leaves `L`: what a type-driven interpreter asks of
the syntax. -/
inductive Skeleton (N : Type v) (L : Type w) : Type (max v w)
  /-- A leaf. -/
  | leaf (x : L) : Skeleton N L
  /-- A unary node. -/
  | unary (n : N) (s : Skeleton N L) : Skeleton N L
  /-- A binary node. -/
  | binary (n : N) (s₁ s₂ : Skeleton N L) : Skeleton N L

/-- What the semantics reads off a node of the syntax: a plain branching node, an island, or the
index a moved phrase leaves. -/
inductive Node where
  /-- A plain node. -/
  | branch
  /-- An island for continuations. -/
  | island
  /-- The index `n` of a moved phrase. -/
  | index (n : ℕ)
  deriving DecidableEq, Repr

end Interpreter
