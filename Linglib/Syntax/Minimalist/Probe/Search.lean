module

public import Linglib.Syntax.Minimalist.Probe.SyntacticObject
public import Mathlib.Data.List.Lex

/-!
# Search orders

A probe's search can be stated procedurally, as the order in which it considers the positions of
its domain, stopping at the first one that satisfies it; such an order is a key for
`PlanarSyntacticObject.goalsBy`. Depth-first search, left to right, orders positions
lexicographically by their paths, the preorder of `RoseTree.vertices`; breadth-first search orders
them by depth and then left to right; and breadth-first search over unordered sisters orders them
by depth alone.

## Main definitions

* `Minimalist.Probe.depthFirst`, `Minimalist.Probe.breadthFirst`: the two ordered searches; search
  over unordered sisters is by `GornAddress.depth`.

## References

* [branan-erlewine-2026]
-/

@[expose] public section

namespace Minimalist.Probe


/-- Depth-first search, left to right: the lexicographic order on paths, which considers a node
before the nodes it dominates and the nodes of a left daughter before those of its sister. -/
def depthFirst (q : GornAddress) : List ℕ := q.toList

/-- Breadth-first search, left to right: by depth, then left to right. -/
def breadthFirst (q : GornAddress) : ℕ ×ₗ List ℕ := toLex (q.depth, q.toList)

theorem breadthFirst_lt_of_depth_lt {a b : GornAddress} (h : a.depth < b.depth) :
    breadthFirst a < breadthFirst b :=
  Prod.Lex.toLex_lt_toLex.2 (.inl h)

theorem depth_complement {b : GornAddress} (hb : b ≠ ⊥) : (complement b).depth = b.depth := by
  have : b.toList ≠ [] := fun h ↦ hb (GornAddress.ext h)
  simp only [GornAddress.depth, complement, List.length_append, List.length_dropLast,
    List.length_singleton]
  have := List.length_pos_iff.2 this
  omega

end Minimalist.Probe
