/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Decidable adjacency in a disjoint sum

`[UPSTREAM]` candidate for `Mathlib/Combinatorics/SimpleGraph/Sum.lean`: the adjacency of a
disjoint sum of two graphs with decidable adjacency is decidable.
-/

@[expose] public section

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

instance [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj
  | .inl _, .inl _ => decidable_of_iff' _ sum_adj_inl
  | .inr _, .inr _ => decidable_of_iff' _ sum_adj_inr
  | .inl _, .inr _ => isFalse (by simp)
  | .inr _, .inl _ => isFalse (by simp)

end SimpleGraph
