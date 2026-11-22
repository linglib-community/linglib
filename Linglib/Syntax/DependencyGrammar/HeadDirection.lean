/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.DependencyGrammar.Basic
public import Linglib.Syntax.WordOrder

/-!
# Head direction of a dependency structure

A dependency structure has head direction `d` when every dependent lies in direction `d` of its
head: after it if `d` is head-initial, before it if `d` is head-final. The mirror image of a
structure has the opposite head direction, and a structure with a head direction keeps it when
arcs are removed, so the arcs bearing one relation of a labelled graph may have a head direction
that the whole graph lacks.

## Main definitions

* `Digraph.HasDirection`: every arc runs in the given direction.
-/

@[expose] public section

namespace Digraph

variable {V : Type*} [LT V] {n : ℕ} {d : HeadDirection}

/-- A digraph on ordered vertices has head direction `d` when every dependent lies in direction
`d` of its head, after it if `d` is head-initial and before it if `d` is head-final. -/
def HasDirection (G : Digraph V) (d : HeadDirection) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → d.Orders v w

instance [Fintype V] [DecidableLT V] (G : Digraph V) [DecidableRel G.Adj] (d : HeadDirection) :
    Decidable (G.HasDirection d) :=
  inferInstanceAs (Decidable (∀ v w, G.Adj v w → d.Orders v w))

theorem HasDirection.mono {G H : Digraph V} (h : G ≤ H) (hH : H.HasDirection d) :
    G.HasDirection d :=
  fun _ _ hvw ↦ hH (h hvw)

theorem hasDirection_mirror {G : Digraph (Fin n)} :
    G.mirror.HasDirection d ↔ G.HasDirection d.swap := by
  have key : ∀ v w : Fin n, d.Orders v.rev w.rev ↔ d.swap.Orders v w := by
    cases d <;> simp
  refine ⟨fun h v w hvw ↦ (key v w).1 (h (by simpa using hvw)), fun h v w hvw ↦ ?_⟩
  simpa using (key v.rev w.rev).2 (h hvw)

theorem HasDirection.mirror {G : Digraph (Fin n)} (h : G.HasDirection d) :
    G.mirror.HasDirection d.swap :=
  hasDirection_mirror.2 (by simpa using h)

end Digraph
