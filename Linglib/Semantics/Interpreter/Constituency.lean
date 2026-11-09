module

public import Linglib.Syntax.Tree.Basic
public import Linglib.Semantics.Interpreter.Mode

/-!
# The bare structure of a constituency tree

A constituency tree gives the semantics its words in their constituency and order, the indices of
its moved phrases, and which of its nodes are islands. A terminal is a leaf, a trace a leaf that
is its index, a binder the index over its body, a non-branching node its daughter, and a binary
node a plain node or, at a category that is an island, an island.

## Main definitions

* `PhraseStructure.Tree.skeleton`: the bare structure of a tree.

## References

* [bumford-charlow-2026]
* [heim-kratzer-1998]
-/

@[expose] public section

namespace PhraseStructure.Tree

open Interpreter Interpreter.Grammar

variable {C L : Type}

/-- The bare structure of a tree, with the categories `island` holds of as islands: its leaves are
words and trace indices, and it has none if a phrase has no daughter or more than two. -/
def skeleton (island : C → Bool) : Tree C L → Option (Skeleton Node (L ⊕ ℕ))
  | .terminal _ w => some (.leaf (.inl w))
  | .trace n _ => some (.leaf (.inr n))
  | .bind n _ body => (skeleton island body).map (.unary (.index n))
  | .phrase _ _ (t :: []) => skeleton island t
  | .phrase c _ (t₁ :: t₂ :: []) => do
    let s₁ ← skeleton island t₁
    let s₂ ← skeleton island t₂
    pure (.binary (if island c then .island else .branch) s₁ s₂)
  | _ => none

end PhraseStructure.Tree
