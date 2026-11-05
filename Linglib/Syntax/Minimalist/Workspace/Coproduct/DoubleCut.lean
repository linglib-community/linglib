/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Workspace.Coproduct.TraceCut
public import Linglib.Core.Data.UnorderedTree.Basic
public import Mathlib.Tactic.Abel

/-!
# Double cuts

Both composites `(Δ^c ⊗ id) ∘ Δ^c` and `(id ⊗ Δ^c) ∘ Δ^c` enumerate the pairs of nested admissible
cuts of a tree, the second cut taken in the crown (`doubleCutsCrown`) or in the trunk
(`doubleCutsTrunk`) of the first. For a coherent trace encoder [the two enumerations agree up to the
order of children](##doubleCuts_eq). This file proves the agreement on rose trees, where the cut
enumeration recurses structurally, and `Trace.lean` descends it to `UnorderedTree`, where it is the
coassociativity of the coproduct `Δ^c` of Marcolli, Chomsky and Berwick (their Lemma 1.2.10, p. 37).
Trace coherence enters at [one child](##childDoubleCuts_eq), where it reconciles the marker a deeper
cut writes on a trunk.

## References

* [marcolli-chomsky-berwick-2025]
* [foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree UnorderedTree

namespace ConnesKreimer

/-! ### Double cuts over a cut enumeration -/

section Enumeration

variable {γ δ : Type*}

/-- The nested cuts of `t` whose second cut is in the crown of the first. -/
def doubleCutsCrown (cuts : γ → Multiset (Multiset γ × γ)) (t : γ) :
    Multiset (Multiset γ × Multiset γ × Multiset γ) :=
  (treeCuts cuts t).bind fun p ↦ (forestCuts cuts p.1).map fun q ↦ (q.1, q.2, p.2)

/-- The nested cuts of `t` whose second cut is in the trunk of the first. -/
def doubleCutsTrunk (cuts : γ → Multiset (Multiset γ × γ)) (t : γ) :
    Multiset (Multiset γ × Multiset γ × Multiset γ) :=
  (treeCuts cuts t).bind fun p ↦ (forestCuts cuts p.2).map fun q ↦ (p.1, q.1, q.2)

variable {cuts : γ → Multiset (Multiset γ × γ)} {cuts' : δ → Multiset (Multiset δ × δ)} {f : γ → δ}

/-- A map carrying one enumeration to another carries the double cuts through the crown along. -/
theorem doubleCutsCrown_map (h : ∀ t, cuts' (f t) = (cuts t).map (Prod.map (Multiset.map f) f))
    (t : γ) :
    doubleCutsCrown cuts' (f t) =
      (doubleCutsCrown cuts t).map fun q ↦ (q.1.map f, q.2.1.map f, q.2.2.map f) := by
  rw [doubleCutsCrown, treeCuts_map h, Multiset.bind_map, doubleCutsCrown, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ ↦ ?_
  rw [Prod.map_fst, forestCuts_map h, Multiset.map_map, Multiset.map_map]
  rfl

/-- A map carrying one enumeration to another carries the double cuts through the trunk along. -/
theorem doubleCutsTrunk_map (h : ∀ t, cuts' (f t) = (cuts t).map (Prod.map (Multiset.map f) f))
    (t : γ) :
    doubleCutsTrunk cuts' (f t) =
      (doubleCutsTrunk cuts t).map fun q ↦ (q.1.map f, q.2.1.map f, q.2.2.map f) := by
  rw [doubleCutsTrunk, treeCuts_map h, Multiset.bind_map, doubleCutsTrunk, Multiset.map_bind]
  refine Multiset.bind_congr fun p _ ↦ ?_
  rw [Prod.map_snd, forestCuts_map h, Multiset.map_map, Multiset.map_map]
  rfl

end Enumeration

/-! ### Double cuts at the trace policy -/

variable {α β : Type*} (τ : RoseTree (α ⊕ β) → β)

/-- Forests of rose trees. -/
local notation "𝓕" => Multiset (RoseTree (α ⊕ β))

/-- Lists of children. -/
local notation "𝓛" => List (RoseTree (α ⊕ β))

/-- The cuts of a list of children at the trace policy, which keep the trace leaves of a cut. -/
local notation "𝒞" => childrenCuts (leaveTrace τ)

/-- The cuts of a tree with the trunk as a forest, at the trace policy. -/
local notation "𝒯" => treeCuts (rootCuts (leaveTrace τ))

/-- The cuts of a forest, at the trace policy. -/
local notation "ℱ" => forestCuts (rootCuts (leaveTrace τ))

/-- Projection of a triple of forests to unordered trees. -/
def projTriple (q : 𝓕 × 𝓕 × 𝓕) :
    Multiset (UnorderedTree (α ⊕ β)) × Multiset (UnorderedTree (α ⊕ β)) ×
      Multiset (UnorderedTree (α ⊕ β)) :=
  (q.1.map UnorderedTree.mk, q.2.1.map UnorderedTree.mk, q.2.2.map UnorderedTree.mk)

/-- The cuts of a node are the full cut and the cuts of its children under `node a`. -/
private theorem treeCuts_node (a : α ⊕ β) (cs : 𝓛) :
    𝒯 (RoseTree.node a cs) =
      (({RoseTree.node a cs} : 𝓕), (0 : 𝓕)) ::ₘ
        (𝒞 cs).map fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕)) := by
  rw [treeCuts, rootCuts_node, Multiset.map_map]
  rfl

/-- The double cuts of a node through the crown: the full cut, its re-cuts, and the re-cuts of the
    crowns of the cuts of its children. -/
private theorem doubleCutsCrown_node (a : α ⊕ β) (cs : 𝓛) :
    doubleCutsCrown (rootCuts (leaveTrace τ)) (RoseTree.node a cs) =
      ((({RoseTree.node a cs} : 𝓕), (0 : 𝓕), (0 : 𝓕)) ::ₘ
        (𝒞 cs).map fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕), (0 : 𝓕)))
      + (𝒞 cs).bind fun p ↦ (ℱ p.1).map fun q ↦ (q.1, q.2, ({RoseTree.node a p.2} : 𝓕)) := by
  rw [doubleCutsCrown, treeCuts_node, Multiset.cons_bind, Multiset.bind_map]
  simp only [forestCuts_singleton, treeCuts_node, Multiset.map_cons, Multiset.map_map]
  rfl

/-- The double cuts of a node through the trunk: the full cut, and for each cut of its children
    the re-cuts of the trunk. -/
private theorem doubleCutsTrunk_node (a : α ⊕ β) (cs : 𝓛) :
    doubleCutsTrunk (rootCuts (leaveTrace τ)) (RoseTree.node a cs) =
      {(({RoseTree.node a cs} : 𝓕), (0 : 𝓕), (0 : 𝓕))}
      + (𝒞 cs).bind fun p ↦ (𝒯 (RoseTree.node a p.2)).map fun q ↦ (p.1, q.1, q.2) := by
  rw [doubleCutsTrunk, treeCuts_node, Multiset.cons_bind, Multiset.bind_map]
  simp only [forestCuts_zero, forestCuts_singleton, Multiset.map_singleton]

/-! ### Double cuts of a list of children

`recutCrown` and `recutRemainder` re-cut the crown and the remainder of a cut of a list of children.
Projected through `projTripleList`, each is multiplicative over the combination of cuts in
`childrenCuts_cons`. -/

/-- Projection of a (crown, mid, remainder-list) triple to nonplanar. -/
def projTripleList (q : 𝓕 × 𝓕 × 𝓛) :
    Multiset (UnorderedTree (α ⊕ β)) × Multiset (UnorderedTree (α ⊕ β)) ×
      Multiset (UnorderedTree (α ⊕ β)) :=
  (q.1.map UnorderedTree.mk, q.2.1.map UnorderedTree.mk,
    Multiset.ofList (q.2.2.map UnorderedTree.mk))

private theorem projTripleList_add (a a' b b' : 𝓕) (l l' : 𝓛) :
    projTripleList (a + a', b + b', l ++ l') =
      projTripleList (a, b, l) + projTripleList (a', b', l') := by
  unfold projTripleList
  rw [Multiset.map_add, Multiset.map_add, List.map_append]
  rfl

/-- LHS children-list double cut: re-cut crown `p.1`, keep remainder `p.2`. -/
def recutCrown (S : Multiset (𝓕 × 𝓛)) :
    Multiset (𝓕 × 𝓕 × 𝓛) :=
  S.bind (fun p ↦ (ℱ p.1).map (fun c12 ↦ (c12.1, c12.2, p.2)))

/-- RHS children-list double cut: keep crown `p.1`, re-cut remainder `p.2`. -/
def recutRemainder (S : Multiset (𝓕 × 𝓛)) :
    Multiset (𝓕 × 𝓕 × 𝓛) :=
  S.bind (fun p ↦ (𝒞 p.2).map (fun q ↦ (p.1, q.1, q.2)))

private theorem map_projTripleList_recutCrown (S : Multiset (𝓕 × 𝓛)) :
    (recutCrown τ S).map projTripleList =
      S.bind (fun p ↦ (ℱ p.1).map (fun c12 ↦ projTripleList (c12.1, c12.2, p.2))) := by
  unfold recutCrown; rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl

private theorem map_projTripleList_recutRemainder (S : Multiset (𝓕 × 𝓛)) :
    (recutRemainder τ S).map projTripleList =
      S.bind (fun p ↦ (𝒞 p.2).map (fun q ↦ projTripleList (p.1, q.1, q.2))) := by
  unfold recutRemainder; rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl

/-- Re-cutting a combined crown with a combined remainder is the convolution of the parts. -/
private theorem map_projTripleList_crown_add (s t : 𝓕 × 𝓛) :
    (ℱ (s.1 + t.1)).map (fun c12 ↦ projTripleList (c12.1, c12.2, s.2 ++ t.2))
      = Multiset.conv ((ℱ s.1).map (fun c12 ↦ projTripleList (c12.1, c12.2, s.2)))
              ((ℱ t.1).map (fun c12 ↦ projTripleList (c12.1, c12.2, t.2))) := by
  rw [forestCuts_add]
  exact Multiset.map_conv (f := fun c : 𝓕 × 𝓕 ↦ projTripleList (c.1, c.2, s.2))
    (f' := fun c : 𝓕 × 𝓕 ↦ projTripleList (c.1, c.2, t.2))
    (g := fun c : 𝓕 × 𝓕 ↦ projTripleList (c.1, c.2, s.2 ++ t.2)) _ _
    fun x y ↦ projTripleList_add x.1 y.1 x.2 y.2 s.2 t.2

/-- Re-cutting an appended remainder with a combined crown is the convolution of the parts. -/
private theorem map_projTripleList_remainder_add (s t : 𝓕 × 𝓛) :
    (𝒞 (s.2 ++ t.2)).map (fun q ↦ projTripleList (s.1 + t.1, q.1, q.2))
      = Multiset.conv ((𝒞 s.2).map (fun q ↦ projTripleList (s.1, q.1, q.2)))
              ((𝒞 t.2).map (fun q ↦ projTripleList (t.1, q.1, q.2))) := by
  rw [childrenCuts_append, Multiset.map_map]
  unfold Multiset.conv
  rw [← Multiset.prodMap_map_product, Multiset.map_map]
  apply Multiset.map_congr rfl; rintro ⟨qs, qt⟩ _
  exact projTripleList_add s.1 t.1 qs.1 qt.1 qs.2 qt.2

private theorem recutCrown_conv (S T : Multiset (𝓕 × 𝓛)) :
    (recutCrown τ ((S ×ˢ T).map fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2))).map projTripleList =
      Multiset.conv ((recutCrown τ S).map projTripleList)
        ((recutCrown τ T).map projTripleList) := by
  rw [map_projTripleList_recutCrown, map_projTripleList_recutCrown, map_projTripleList_recutCrown]
  exact Multiset.bind_map_product (c := fun a b ↦ (a.1 + b.1, a.2 ++ b.2))
    (map_projTripleList_crown_add τ) S T

private theorem recutRemainder_conv (S T : Multiset (𝓕 × 𝓛)) :
    (recutRemainder τ ((S ×ˢ T).map fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2))).map projTripleList =
      Multiset.conv ((recutRemainder τ S).map projTripleList)
        ((recutRemainder τ T).map projTripleList) := by
  rw [map_projTripleList_recutRemainder, map_projTripleList_recutRemainder,
    map_projTripleList_recutRemainder]
  exact Multiset.bind_map_product (c := fun a b ↦ (a.1 + b.1, a.2 ++ b.2))
    (map_projTripleList_remainder_add τ) S T

/-! ### Coassociativity on a list of children

`childrenDoubleCuts_eq` is proved by induction on the list, from the multiplicativity above and
`childDoubleCuts_eq` at each child. `childDoubleCuts_eq` reduces to `childrenDoubleCuts_eq` at the
child's children, with trace coherence reconciling the marker of a child cut whole. -/

/-- Projecting a triple whose remainder is a singleton `[node a' l]` equals
    nonplanar `node a'`-wrapping the projection with raw remainder `l`. -/
private theorem projTripleList_list_wrap (a' : α ⊕ β) (x y : 𝓕) (l : 𝓛) :
    projTripleList (x, y, [RoseTree.node a' l])
      = ((projTripleList (x, y, l)).1, (projTripleList (x, y, l)).2.1,
          ({UnorderedTree.node a' (projTripleList (x, y, l)).2.2} :
            Multiset (UnorderedTree (α ⊕ β)))) := by
  unfold projTripleList
  simp only [List.map_cons, List.map_nil]
  rw [show (Multiset.ofList [UnorderedTree.mk (RoseTree.node a' l)])
        = ({UnorderedTree.mk (RoseTree.node a' l)} : Multiset (UnorderedTree (α ⊕ β))) from rfl,
      ← UnorderedTree.node_mk_tree_list]

/-- The `[node a']`-wrapped `recutCrown` of the children cut, projected, equals the
    nonplanar `node a'`-wrap of the projected `recutCrown`. -/
private theorem recutCrown_node (a' : α ⊕ β) (cs'' : 𝓛) :
    (recutCrown τ
      ((𝒞 cs'').map
        (fun p ↦ (p.1, ([RoseTree.node a' p.2] : 𝓛))))).map projTripleList
      = ((recutCrown τ (𝒞 cs'')).map projTripleList).map
          (fun z ↦ (z.1, z.2.1,
            ({UnorderedTree.node a' z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [map_projTripleList_recutCrown, map_projTripleList_recutCrown, Multiset.bind_map,
    Multiset.map_bind]
  apply Multiset.bind_congr; intro p _
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl; intro c12 _
  exact projTripleList_list_wrap a' c12.1 c12.2 p.2

/-- Re-cutting the trunks of the cuts inside a child, projected, equals the
    nonplanar `node a'`-wrap of the projected `recutRemainder`. -/
private theorem recutRemainder_node (a' : α ⊕ β) (cs'' : 𝓛) :
    ((𝒞 cs'').bind (fun p ↦ (𝒞 p.2).map
        (fun p'' ↦ (p.1, p''.1, ([RoseTree.node a' p''.2] : 𝓛))))).map projTripleList
      = ((recutRemainder τ (𝒞 cs'')).map projTripleList).map
          (fun z ↦ (z.1, z.2.1,
            ({UnorderedTree.node a' z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [map_projTripleList_recutRemainder, Multiset.map_bind, Multiset.map_bind]
  apply Multiset.bind_congr; intro p _
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; intro p'' _
  exact projTripleList_list_wrap a' p.1 p''.1 p''.2

/-- `recutCrown` distributes over a `cons` outer cut. -/
private theorem recutCrown_cons (F : 𝓕) (l : 𝓛)
    (S : Multiset (𝓕 × 𝓛)) :
    recutCrown τ ((F, l) ::ₘ S)
      = (ℱ F).map (fun c12 ↦ (c12.1, c12.2, l)) + recutCrown τ S := by
  unfold recutCrown; rw [Multiset.cons_bind]

/-- `recutRemainder` distributes over a `cons` outer cut. -/
private theorem recutRemainder_cons (F : 𝓕) (l : 𝓛)
    (S : Multiset (𝓕 × 𝓛)) :
    recutRemainder τ ((F, l) ::ₘ S)
      = (𝒞 l).map (fun q ↦ (F, q.1, q.2)) + recutRemainder τ S := by
  unfold recutRemainder; rw [Multiset.cons_bind]

/-! **Children-list coassoc** (`childrenDoubleCuts_eq`) and **per-child coassoc**
    (`childDoubleCuts_eq`), proved by mutual structural recursion mirroring
    `childrenCuts`/`childCuts`. `childrenDoubleCuts_eq` is the engine of the per-tree
    node step; `childDoubleCuts_eq` is the coherence-using combinatorial core. -/
mutual
theorem childrenDoubleCuts_eq (hτ : ∀ t, ∀ p ∈ rootCuts (leaveTrace τ) t, τ p.2 = τ t) :
    ∀ cs : 𝓛,
      (recutCrown τ (𝒞 cs)).map projTripleList = (recutRemainder τ (𝒞 cs)).map projTripleList
  | [] => by
    rw [childrenCuts_nil]
    unfold recutCrown recutRemainder
    rw [Multiset.singleton_bind, Multiset.singleton_bind, forestCuts_zero, childrenCuts_nil]
    simp only [Multiset.map_singleton]
  | c :: cs' => by
    rw [childrenCuts_cons, recutCrown_conv, recutRemainder_conv, childDoubleCuts_eq hτ c,
      childrenDoubleCuts_eq hτ cs']
theorem childDoubleCuts_eq (hτ : ∀ t, ∀ p ∈ rootCuts (leaveTrace τ) t, τ p.2 = τ t) :
    ∀ c : RoseTree (α ⊕ β),
      (recutCrown τ (childCuts (leaveTrace τ) c)).map projTripleList
        = (recutRemainder τ (childCuts (leaveTrace τ) c)).map projTripleList
  | .node a' cs'' => by
    have hchildren := childrenDoubleCuts_eq hτ cs''
    cases a' with
    | inr b' =>
      -- A trace is never cut whole, so coherence is not needed.
      rw [show childCuts (leaveTrace τ) (RoseTree.node (Sum.inr b') cs'')
            = (𝒞 cs'').map (fun p ↦ (p.1, ([RoseTree.node (Sum.inr b') p.2]
                : 𝓛))) from by
          rw [childCuts_eq_none _ _ (leaveTrace_inr τ b' cs''), rootCuts_node,
              Multiset.map_map]; rfl]
      have hdcr : recutRemainder τ ((𝒞 cs'').map
            (fun p ↦ (p.1, ([RoseTree.node (Sum.inr b') p.2] : 𝓛))))
          = (𝒞 cs'').bind (fun p ↦ (𝒞 p.2).map
              (fun p'' ↦ (p.1, p''.1, [RoseTree.node (Sum.inr b') p''.2]))) := by
        unfold recutRemainder; rw [Multiset.bind_map]
        apply Multiset.bind_congr; intro p _
        rw [show 𝒞 [RoseTree.node (Sum.inr b') p.2] = (𝒞 p.2).map
              (fun p'' ↦ (p''.1, [RoseTree.node (Sum.inr b') p''.2])) from by
            rw [childrenCuts_singleton, childCuts_eq_none _ _ (leaveTrace_inr τ b' p.2),
                rootCuts_node, Multiset.map_map]; rfl,
          Multiset.map_map]
        rfl
      rw [recutCrown_node, hdcr, recutRemainder_node, hchildren]
    | inl a'' =>
      have hAa : childCuts (leaveTrace τ) (RoseTree.node (Sum.inl a'') cs'')
          = (({RoseTree.node (Sum.inl a'') cs''} : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]) ::ₘ
              (𝒞 cs'').map (fun p ↦ (p.1, [RoseTree.node (Sum.inl a'') p.2])) := by
        rw [childCuts_eq_some _ _ _ (leaveTrace_inl τ a'' cs''), rootCuts_node,
            Multiset.map_map]; rfl
      have hCltl : 𝒞 [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]
          = {((0 : 𝓕), [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))])} := by
        rw [childrenCuts_singleton]
        show childCuts (leaveTrace τ)
              (RoseTree.node (Sum.inr (τ (RoseTree.node (Sum.inl a'') cs''))) [])
            = {((0 : 𝓕),
                [RoseTree.node (Sum.inr (τ (RoseTree.node (Sum.inl a'') cs''))) []])}
        rw [childCuts_eq_none _ _ (leaveTrace_inr τ _ []), rootCuts_node,
            childrenCuts_nil]; rfl
      have hdcr : recutRemainder τ ((𝒞 cs'').map
            (fun p ↦ (p.1, [RoseTree.node (Sum.inl a'') p.2])))
          = (𝒞 cs'').map (fun p ↦ (p.1, ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
                [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]))
            + (𝒞 cs'').bind (fun p ↦ (𝒞 p.2).map
                (fun p'' ↦ (p.1, p''.1, [RoseTree.node (Sum.inl a'') p''.2]))) := by
        have step1 : recutRemainder τ ((𝒞 cs'').map
              (fun p ↦ (p.1, [RoseTree.node (Sum.inl a'') p.2])))
            = (𝒞 cs'').bind (fun p ↦
                (p.1, ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
                  [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]) ::ₘ
                (𝒞 p.2).map (fun p'' ↦
                  (p.1, p''.1, [RoseTree.node (Sum.inl a'') p''.2]))) := by
          unfold recutRemainder; rw [Multiset.bind_map]
          apply Multiset.bind_congr; intro p _
          show (𝒞 [RoseTree.node (Sum.inl a'') p.2]).map
              (fun q ↦ (p.1, q.1, q.2)) = _
          rw [show 𝒞 [RoseTree.node (Sum.inl a'') p.2]
                = (({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
                    [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]) ::ₘ
                  (𝒞 p.2).map (fun p'' ↦
                    (p''.1, [RoseTree.node (Sum.inl a'') p''.2])) from by
              rw [childrenCuts_singleton, childCuts_eq_some _ _ _ (leaveTrace_inl τ a'' p.2),
                  rootCuts_node, Multiset.map_map]; rfl,
            Multiset.map_cons, Multiset.map_map]
          rfl
        rw [step1, Multiset.bind_cons]
      -- Coherence: every trunk of the child writes the marker of the child.
      have hcoh : ((𝒞 cs'').map (fun p : 𝓕 × 𝓛 ↦ (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') p.2))]))).map projTripleList
          = ((𝒞 cs'').map (fun p : 𝓕 × 𝓛 ↦ (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map projTripleList := by
        rw [Multiset.map_map, Multiset.map_map]
        apply Multiset.map_congr rfl; intro p hp
        simp only [Function.comp_apply]
        rw [show τ (RoseTree.node (Sum.inl a'') p.2) = τ (RoseTree.node (Sum.inl a'') cs'') from
          hτ (RoseTree.node (Sum.inl a'') cs'') (p.1, RoseTree.node (Sum.inl a'') p.2)
            (by rw [rootCuts_node]; exact Multiset.mem_map.mpr ⟨p, hp, rfl⟩)]
      -- Re-cutting the child cut whole gives the full cut and the cuts inside it.
      have hΦrecutCrown : ((ℱ {RoseTree.node (Sum.inl a'') cs''}).map
            (fun c12 ↦ (c12.1, c12.2,
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map projTripleList
          = projTripleList (({RoseTree.node (Sum.inl a'') cs''} : 𝓕), (0 : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]) ::ₘ
            ((𝒞 cs'').map (fun p : 𝓕 × 𝓛 ↦ (p.1,
              ({RoseTree.node (Sum.inl a'') p.2} : 𝓕),
              [traceLeaf (τ (RoseTree.node (Sum.inl a'') cs''))]))).map projTripleList := by
        rw [forestCuts_singleton, treeCuts_node, Multiset.map_cons, Multiset.map_map,
            Multiset.map_cons]
        rfl
      rw [hAa, recutCrown_cons, recutRemainder_cons, hCltl, Multiset.map_singleton,
          Multiset.map_add, Multiset.map_add, recutCrown_node, hdcr, Multiset.map_add,
          recutRemainder_node, hcoh, hchildren, hΦrecutCrown, Multiset.map_singleton]
      simp only [← Multiset.singleton_add]
      abel
end

/-! ### Per-tree coassoc `doubleCuts_eq` from `childrenDoubleCuts_eq` (node reduction + root wrap)
-/

/-- Projecting a `node a`-wrapped triple equals nonplanar-wrapping the
    projected triple. -/
private theorem projTriple_node_wrap (a : α ⊕ β)
    (q : 𝓕 × 𝓕 × 𝓛) :
    projTriple (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕))
      = ((projTripleList q).1, (projTripleList q).2.1,
          ({UnorderedTree.node a (projTripleList q).2.2} : Multiset (UnorderedTree (α ⊕ β)))) := by
  unfold projTriple projTripleList
  simp only [Multiset.map_singleton]
  rw [UnorderedTree.node_mk_tree_list]

/-- The `node a`-wrap on planar triples, projected, equals the nonplanar
    `node a`-wrap on projected triples. -/
private theorem map_node_wrap_projTriple (a : α ⊕ β)
    (M : Multiset (𝓕 × 𝓕 × 𝓛)) :
    (M.map (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))).map projTriple
      = (M.map projTripleList).map (fun z ↦ (z.1, z.2.1,
          ({UnorderedTree.node a z.2.2} : Multiset (UnorderedTree (α ⊕ β))))) := by
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; intro q _
  exact projTriple_node_wrap a q

theorem doubleCuts_eq (hτ : ∀ t, ∀ p ∈ rootCuts (leaveTrace τ) t, τ p.2 = τ t)
    (t : RoseTree (α ⊕ β)) :
    (doubleCutsCrown (rootCuts (leaveTrace τ)) t).map projTriple =
      (doubleCutsTrunk (rootCuts (leaveTrace τ)) t).map projTriple := by
  obtain ⟨a, cs⟩ := t
  -- Core: the two genuine remainder re-cuts agree (= `childrenDoubleCuts_eq` wrapped by `node a`).
  have hcore : ((𝒞 cs).bind (fun p ↦ (ℱ p.1).map
        (fun c12 ↦ (c12.1, c12.2, ({RoseTree.node a p.2} : 𝓕))))).map projTriple
      = ((𝒞 cs).bind (fun p ↦ (𝒞 p.2).map
        (fun q ↦ (p.1, q.1, ({RoseTree.node a q.2} : 𝓕))))).map projTriple := by
    rw [show ((𝒞 cs).bind (fun p ↦ (ℱ p.1).map
            (fun c12 ↦ (c12.1, c12.2, ({RoseTree.node a p.2} : 𝓕)))))
          = ((recutCrown τ (𝒞 cs)).map
              (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))) from by
        unfold recutCrown; rw [Multiset.map_bind]
        apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl,
      show ((𝒞 cs).bind (fun p ↦ (𝒞 p.2).map
            (fun q ↦ (p.1, q.1, ({RoseTree.node a q.2} : 𝓕)))))
          = ((recutRemainder τ (𝒞 cs)).map
              (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))) from by
        unfold recutRemainder; rw [Multiset.map_bind]
        apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl]
    rw [map_node_wrap_projTriple, map_node_wrap_projTriple, childrenDoubleCuts_eq τ hτ cs]
  rw [doubleCutsCrown_node, doubleCutsTrunk_node]
  rw [show (fun p : 𝓕 × 𝓛 ↦
        (𝒯 (RoseTree.node a p.2)).map (fun B12 ↦ (p.1, B12.1, B12.2)))
        = (fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕), (0 : 𝓕)) ::ₘ
            (𝒞 p.2).map (fun q ↦ (p.1, q.1, ({RoseTree.node a q.2} : 𝓕)))) from by
      funext p
      rw [treeCuts_node, Multiset.map_cons, Multiset.map_map]; rfl]
  rw [Multiset.bind_cons, Multiset.map_add, Multiset.map_add, Multiset.map_add,
      Multiset.map_cons, Multiset.map_singleton, hcore, ← Multiset.singleton_add]
  abel

end ConnesKreimer
