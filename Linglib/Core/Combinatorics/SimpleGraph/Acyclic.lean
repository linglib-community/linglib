/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Leaves of finite forests

`[UPSTREAM]` candidate for `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`: a nonempty forest
with finitely many edges has a vertex with at most one neighbour, the forest analogue of
`SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A nonempty forest with finitely many edges has a vertex with at most one neighbour: an end
of a longest path. -/
theorem IsAcyclic.exists_neighborSet_subsingleton [Nonempty V] [Finite G.edgeSet]
    (hG : G.IsAcyclic) :
    ∃ v, (G.neighborSet v).Subsingleton := by
  obtain ⟨u, v, p, hp, hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length G
  have h {w} (hw : G.Adj u w) : w = p.snd := hG.eq_snd_of_adj_start hp hw <| by_contra fun hw' ↦
    by simpa using hmax _ _ _ (hp.cons hw' (h := hw.symm))
  exact ⟨u, fun w hw w' hw' ↦ (h hw).trans (h hw').symm⟩

end SimpleGraph
