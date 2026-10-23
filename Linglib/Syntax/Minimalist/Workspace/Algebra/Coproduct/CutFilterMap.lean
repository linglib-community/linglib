/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Algebra.Coproduct.TraceCut
public import Linglib.Core.Data.UnorderedTree.FilterMap

/-!
# Trace cuts of a tree without traces

A tree with no trace vertices embeds among the trees with traces along `Sum.inl`. Its trace cuts
(`cutSummandsCN`) are then its pruning cuts (`cutSummandsN`) with a trace leaf left at each cut
site: the crowns are the embedded pruning crowns, and erasing the trace leaves of a trunk with
`UnorderedTree.filterMap Sum.getLeft?` gives back the pruning trunk. This is the combinatorial
content of the relation between the coproducts `Δ^c` and `Δ^ρ` of Marcolli, Chomsky and Berwick,
which `Deletion.lean` states on the algebra.

## Main results

* `ConnesKreimer.cutSummandsCN_map_inl`: the identity, between multisets of pairs of a crown and a
  trunk.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

open RoseTree

namespace ConnesKreimer

variable {α β : Type*}

mutual

private theorem cutSummandsCP_map_inl (τ : RoseTree (α ⊕ β) → β) :
    ∀ t : RoseTree α,
      (cutSummandsCP τ (t.map Sum.inl)).map (Prod.map id (filterMap Sum.getLeft?)) =
        (cutSummandsG pruning t).map (Prod.map (Multiset.map (map Sum.inl)) some)
  | .node a cs => by
    have h := congrArg (Multiset.map fun q : Multiset (RoseTree (α ⊕ β)) × List (RoseTree α) ↦
      (q.1, some (node a q.2))) (cutListSummandsG_map_inl τ cs)
    simpa [Multiset.map_map, Function.comp_def] using h

private theorem cutListSummandsG_map_inl (τ : RoseTree (α ⊕ β) → β) :
    ∀ cs : List (RoseTree α),
      (cutListSummandsG (extractC τ) (cs.map (map Sum.inl))).map
          (Prod.map id (List.filterMap (filterMap Sum.getLeft?))) =
        (cutListSummandsG pruning cs).map (Prod.map (Multiset.map (map Sum.inl)) id)
  | [] => by simp
  | c :: cs => by
    rw [List.map_cons, cutListSummandsG_cons, cutListSummandsG_cons,
      Multiset.map_map_product_distrib (f' := fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2))
        (g₁ := Prod.map id (List.filterMap (filterMap Sum.getLeft?)))
        (g₂ := Prod.map id (List.filterMap (filterMap Sum.getLeft?))) (by simp),
      augActionG_map_inl τ c, cutListSummandsG_map_inl τ cs]
    exact (Multiset.map_map_product_distrib (by simp) _ _).symm

private theorem augActionG_map_inl (τ : RoseTree (α ⊕ β) → β) :
    ∀ c : RoseTree α,
      (augActionG (extractC τ) (c.map Sum.inl)).map
          (Prod.map id (List.filterMap (filterMap Sum.getLeft?))) =
        (augActionG pruning c).map (Prod.map (Multiset.map (map Sum.inl)) id)
  | c => by
    have hc : extractC τ (c.map Sum.inl) = some [traceLeaf (τ (c.map Sum.inl))] := by
      cases c; rfl
    have h := congrArg (Multiset.map fun q : Multiset (RoseTree (α ⊕ β)) × Option (RoseTree α) ↦
      (q.1, q.2.toList)) (cutSummandsCP_map_inl τ c)
    have hL (x : RoseTree (α ⊕ β)) :
        [x].filterMap (filterMap Sum.getLeft?) = (filterMap Sum.getLeft? x).toList := by
      cases hx : filterMap Sum.getLeft? x <;> simp [hx]
    rw [augActionG_eq_some _ _ _ hc, augActionG_eq_some pruning c [] rfl, Multiset.map_cons,
      Multiset.map_cons]
    congr 1
    simpa [Multiset.map_map, Function.comp_def, cutSummandsCP, hL] using h

end

/-- The trace cuts of a tree without traces are its pruning cuts with a trace leaf left at each
    cut site: the crowns agree, and erasing the trace leaves of a trunk gives the pruning trunk. -/
theorem cutSummandsCN_map_inl (τ : UnorderedTree (α ⊕ β) → β) (T : UnorderedTree α) :
    (cutSummandsCN τ (T.map Sum.inl)).map (Prod.map id (UnorderedTree.filterMap Sum.getLeft?)) =
      (cutSummandsN T).map (Prod.map (Multiset.map (UnorderedTree.map Sum.inl)) some) :=
  Quotient.inductionOn T fun t ↦ by
    have h := congrArg
      (Multiset.map (Prod.map (Multiset.map UnorderedTree.mk) (Option.map UnorderedTree.mk)))
      (cutSummandsCP_map_inl (τ ∘ UnorderedTree.mk) t)
    simpa [UnorderedTree.map_mk, projSummand, Multiset.map_map, Function.comp_def,
      Prod.map_apply'] using h

end ConnesKreimer
