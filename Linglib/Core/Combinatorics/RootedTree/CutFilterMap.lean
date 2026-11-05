/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Linglib.Core.Data.RoseTree.FilterMap

/-!
# Cuts under a partial relabelling

The cut enumeration `rootCuts` is natural in its policy. Let `g` relabel trees and let `f`
relabel them partially, dropping the subtrees whose root it sends to `none`. When a policy `E` at
the relabelled trees and a policy `E'` at the original trees leave the same remainders after `f`,
[the cuts of a relabelled tree under `E` are the relabelled cuts under
`E'`](##map_rootCuts_map), the trunks compared after `f`. Policies that differ only in what `f`
drops therefore differ only in the trunks of their cuts.

## References

* [connes-kreimer-1998]
-/

@[expose] public section

open RoseTree

namespace ConnesKreimer

variable {α γ δ : Type*} {E : RoseTree γ → Option (List (RoseTree γ))}
  {E' : RoseTree α → Option (List (RoseTree α))} {g : α → γ} {f : γ → Option δ}

private theorem filterMap_singleton_eq_toList {X Y : Type*} (φ : X → Option Y) (x : X) :
    [x].filterMap φ = (φ x).toList := by
  cases h : φ x <;> simp [h]

mutual

/-- Cuts of a relabelled tree are the relabelled cuts, when the two policies leave the same
    remainders after `f`. The trunks are compared after `f`. -/
theorem map_rootCuts_map
    (hE : ∀ t, (E (t.map g)).map (List.filterMap (filterMap f)) =
      (E' t).map (List.filterMap (filterMap f ∘ map g))) :
    ∀ t : RoseTree α, (rootCuts E (t.map g)).map (Prod.map id (filterMap f)) =
      (rootCuts E' t).map (Prod.map (Multiset.map (map g)) (filterMap f ∘ map g))
  | .node a cs => by
    have h := congrArg (Multiset.map fun q : Multiset (RoseTree γ) × List (RoseTree δ) ↦
      (q.1, (f (g a)).map fun b ↦ node b q.2)) (map_childrenCuts_map hE cs)
    simpa [Multiset.map_map, Function.comp_def, List.filterMap_map] using h

private theorem map_childrenCuts_map
    (hE : ∀ t, (E (t.map g)).map (List.filterMap (filterMap f)) =
      (E' t).map (List.filterMap (filterMap f ∘ map g))) :
    ∀ cs : List (RoseTree α),
      (childrenCuts E (cs.map (map g))).map (Prod.map id (List.filterMap (filterMap f))) =
        (childrenCuts E' cs).map
          (Prod.map (Multiset.map (map g)) (List.filterMap (filterMap f ∘ map g)))
  | [] => by simp
  | c :: cs => by
    rw [List.map_cons, childrenCuts_cons, childrenCuts_cons,
      Multiset.map_map_product_distrib (f' := fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2))
        (g₁ := Prod.map id (List.filterMap (filterMap f)))
        (g₂ := Prod.map id (List.filterMap (filterMap f))) (by simp),
      map_childCuts_map hE c, map_childrenCuts_map hE cs]
    exact (Multiset.map_map_product_distrib (by simp) _ _).symm

private theorem map_childCuts_map
    (hE : ∀ t, (E (t.map g)).map (List.filterMap (filterMap f)) =
      (E' t).map (List.filterMap (filterMap f ∘ map g))) (t : RoseTree α) :
    (childCuts E (t.map g)).map (Prod.map id (List.filterMap (filterMap f))) =
      (childCuts E' t).map
        (Prod.map (Multiset.map (map g)) (List.filterMap (filterMap f ∘ map g))) := by
  have h := congrArg (Multiset.map fun q : Multiset (RoseTree γ) × Option (RoseTree δ) ↦
    (q.1, q.2.toList)) (map_rootCuts_map hE t)
  rw [childCuts_eq, childCuts_eq, Multiset.map_add, Multiset.map_add]
  congr 1
  · have := hE t
    cases h₁ : E (t.map g) <;> cases h₂ : E' t <;> simp_all
  · simpa [Multiset.map_map, Function.comp_def, filterMap_singleton_eq_toList] using h

end

end ConnesKreimer
