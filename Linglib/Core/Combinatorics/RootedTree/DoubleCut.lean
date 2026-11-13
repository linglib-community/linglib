/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Combinatorics.RootedTree.Cut
public import Mathlib.Tactic.Abel

/-!
# Double cuts

A pair of nested cuts of a tree takes its second cut either in the crown of the first
(`doubleCutsCrown`) or in its trunk (`doubleCutsTrunk`). The two composites `(Δ ⊗ id) ∘ Δ` and
`(id ⊗ Δ) ∘ Δ` of an admissible-cut coproduct sum over these two enumerations, so the coproduct
is coassociative when they agree. For the cuts of a [coherent](##ExtractCoherent)
extraction policy [they agree up to the order of children](##doubleCuts_eq), hence
[on unordered trees](##doubleCutsCrown_eq_doubleCutsTrunk); the policy that leaves
nothing is coherent, which gives the
[admissible cuts](##doubleCutsCrown_admissibleCuts). The agreement is proved on
rose trees, where the cut enumeration recurses structurally, and coherence enters at
[one child](##childDoubleCuts_eq), where it reconciles what the policy leaves for
a trunk with what it leaves for the tree the trunk was cut from.

## References

* [foissy-introduction-hopf-algebras-trees]
* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace ConnesKreimer

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

open RoseTree UnorderedTree

/-! ### Double cuts of an extraction policy -/

variable {α : Type*} (extract : RoseTree α → Option (List (RoseTree α)))

/-- A policy is coherent when what it leaves at a cut has no cuts of its own, and cutting inside a
tree does not change what the policy leaves for it. -/
structure ExtractCoherent : Prop where
  childrenCuts_of_eq_some : ∀ t r, extract t = some r → childrenCuts extract r = {(0, r)}
  extract_trunk : ∀ t, ∀ p ∈ rootCuts extract t, extract p.2 = extract t

/-- Forests of rose trees. -/
local notation "𝓕" => Multiset (RoseTree α)

/-- Lists of children. -/
local notation "𝓛" => List (RoseTree α)

/-- The cuts of a list of children under the policy. -/
local notation "𝒞" => childrenCuts (extract)

/-- The cuts of a tree with the trunk as a forest, under the policy. -/
local notation "𝒯" => treeCuts (rootCuts (extract))

/-- The cuts of a forest, under the policy. -/
local notation "ℱ" => forestCuts (rootCuts (extract))

/-- Projection of a triple of forests to unordered trees. -/
def projTriple (q : 𝓕 × 𝓕 × 𝓕) :
    Multiset (UnorderedTree α) × Multiset (UnorderedTree α) ×
      Multiset (UnorderedTree α) :=
  (q.1.map UnorderedTree.mk, q.2.1.map UnorderedTree.mk, q.2.2.map UnorderedTree.mk)

/-- The cuts of a node are the full cut and the cuts of its children under `node a`. -/
private theorem treeCuts_node (a : α) (cs : 𝓛) :
    𝒯 (RoseTree.node a cs) =
      (({RoseTree.node a cs} : 𝓕), (0 : 𝓕)) ::ₘ
        (𝒞 cs).map fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕)) := by
  rw [treeCuts, rootCuts_node, Multiset.map_map]
  rfl

/-- The double cuts of a node through the crown: the full cut, its re-cuts, and the re-cuts of the
    crowns of the cuts of its children. -/
private theorem doubleCutsCrown_node (a : α) (cs : 𝓛) :
    doubleCutsCrown (rootCuts (extract)) (RoseTree.node a cs) =
      ((({RoseTree.node a cs} : 𝓕), (0 : 𝓕), (0 : 𝓕)) ::ₘ
        (𝒞 cs).map fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕), (0 : 𝓕)))
      + (𝒞 cs).bind fun p ↦ (ℱ p.1).map fun q ↦ (q.1, q.2, ({RoseTree.node a p.2} : 𝓕)) := by
  rw [doubleCutsCrown, treeCuts_node, Multiset.cons_bind, Multiset.bind_map]
  simp only [forestCuts_singleton, treeCuts_node, Multiset.map_cons, Multiset.map_map]
  rfl

/-- The double cuts of a node through the trunk: the full cut, and for each cut of its children
    the re-cuts of the trunk. -/
private theorem doubleCutsTrunk_node (a : α) (cs : 𝓛) :
    doubleCutsTrunk (rootCuts (extract)) (RoseTree.node a cs) =
      {(({RoseTree.node a cs} : 𝓕), (0 : 𝓕), (0 : 𝓕))}
      + (𝒞 cs).bind fun p ↦ (𝒯 (RoseTree.node a p.2)).map fun q ↦ (p.1, q.1, q.2) := by
  rw [doubleCutsTrunk, treeCuts_node, Multiset.cons_bind, Multiset.bind_map]
  simp only [forestCuts_zero, forestCuts_singleton, Multiset.map_singleton]

/-! ### Double cuts of a list of children

`recutCrown` and `recutRemainder` re-cut the crown and the remainder of a cut of a list of children.
Projected through `projTripleList`, each is multiplicative over the combination of cuts in
`childrenCuts_cons`. -/

/-- Projection of a triple of a crown, a middle and a list of remaining children to unordered
trees. -/
def projTripleList (q : 𝓕 × 𝓕 × 𝓛) :
    Multiset (UnorderedTree α) × Multiset (UnorderedTree α) ×
      Multiset (UnorderedTree α) :=
  (q.1.map UnorderedTree.mk, q.2.1.map UnorderedTree.mk,
    Multiset.ofList (q.2.2.map UnorderedTree.mk))

private theorem projTripleList_add (a a' b b' : 𝓕) (l l' : 𝓛) :
    projTripleList (a + a', b + b', l ++ l') =
      projTripleList (a, b, l) + projTripleList (a', b', l') := by
  unfold projTripleList
  rw [Multiset.map_add, Multiset.map_add, List.map_append]
  rfl

/-- Re-cut the crown of each cut of a list of children, keeping its remainder. -/
def recutCrown (S : Multiset (𝓕 × 𝓛)) :
    Multiset (𝓕 × 𝓕 × 𝓛) :=
  S.bind (fun p ↦ (ℱ p.1).map (fun c12 ↦ (c12.1, c12.2, p.2)))

/-- Re-cut the remainder of each cut of a list of children, keeping its crown. -/
def recutRemainder (S : Multiset (𝓕 × 𝓛)) :
    Multiset (𝓕 × 𝓕 × 𝓛) :=
  S.bind (fun p ↦ (𝒞 p.2).map (fun q ↦ (p.1, q.1, q.2)))

private theorem map_projTripleList_recutCrown (S : Multiset (𝓕 × 𝓛)) :
    (recutCrown extract S).map projTripleList =
      S.bind (fun p ↦ (ℱ p.1).map (fun c12 ↦ projTripleList (c12.1, c12.2, p.2))) := by
  unfold recutCrown; rw [Multiset.map_bind]
  apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl

private theorem map_projTripleList_recutRemainder (S : Multiset (𝓕 × 𝓛)) :
    (recutRemainder extract S).map projTripleList =
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
    (recutCrown extract ((S ×ˢ T).map fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2))).map projTripleList =
      Multiset.conv ((recutCrown extract S).map projTripleList)
        ((recutCrown extract T).map projTripleList) := by
  rw [map_projTripleList_recutCrown, map_projTripleList_recutCrown, map_projTripleList_recutCrown]
  exact Multiset.bind_map_product (c := fun a b ↦ (a.1 + b.1, a.2 ++ b.2))
    (map_projTripleList_crown_add extract) S T

private theorem recutRemainder_conv (S T : Multiset (𝓕 × 𝓛)) :
    (recutRemainder extract
        ((S ×ˢ T).map fun p ↦ (p.1.1 + p.2.1, p.1.2 ++ p.2.2))).map projTripleList =
      Multiset.conv ((recutRemainder extract S).map projTripleList)
        ((recutRemainder extract T).map projTripleList) := by
  rw [map_projTripleList_recutRemainder, map_projTripleList_recutRemainder,
    map_projTripleList_recutRemainder]
  exact Multiset.bind_map_product (c := fun a b ↦ (a.1 + b.1, a.2 ++ b.2))
    (map_projTripleList_remainder_add extract) S T

/-! ### Coassociativity on a list of children

`childrenDoubleCuts_eq` is proved by induction on the list, from the multiplicativity above and
`childDoubleCuts_eq` at each child. `childDoubleCuts_eq` reduces to `childrenDoubleCuts_eq` at the
child's children, with coherence of the policy reconciling what a child cut whole leaves. -/

/-- Projecting a triple whose remainder is a singleton `[node a' l]` equals
    nonplanar `node a'`-wrapping the projection with raw remainder `l`. -/
private theorem projTripleList_list_wrap (a' : α) (x y : 𝓕) (l : 𝓛) :
    projTripleList (x, y, [RoseTree.node a' l])
      = ((projTripleList (x, y, l)).1, (projTripleList (x, y, l)).2.1,
          ({UnorderedTree.node a' (projTripleList (x, y, l)).2.2} :
            Multiset (UnorderedTree α))) := by
  unfold projTripleList
  simp only [List.map_cons, List.map_nil]
  rw [show (Multiset.ofList [UnorderedTree.mk (RoseTree.node a' l)])
        = ({UnorderedTree.mk (RoseTree.node a' l)} : Multiset (UnorderedTree α)) from rfl,
      ← UnorderedTree.node_mk_tree_list]

/-- The `[node a']`-wrapped `recutCrown` of the children cut, projected, equals the
    nonplanar `node a'`-wrap of the projected `recutCrown`. -/
private theorem recutCrown_node (a' : α) (cs'' : 𝓛) :
    (recutCrown extract
      ((𝒞 cs'').map
        (fun p ↦ (p.1, ([RoseTree.node a' p.2] : 𝓛))))).map projTripleList
      = ((recutCrown extract (𝒞 cs'')).map projTripleList).map
          (fun z ↦ (z.1, z.2.1,
            ({UnorderedTree.node a' z.2.2} : Multiset (UnorderedTree α)))) := by
  rw [map_projTripleList_recutCrown, map_projTripleList_recutCrown, Multiset.bind_map,
    Multiset.map_bind]
  apply Multiset.bind_congr; intro p _
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl; intro c12 _
  exact projTripleList_list_wrap a' c12.1 c12.2 p.2

/-- Re-cutting the trunks of the cuts inside a child, projected, equals the
    nonplanar `node a'`-wrap of the projected `recutRemainder`. -/
private theorem recutRemainder_node (a' : α) (cs'' : 𝓛) :
    ((𝒞 cs'').bind (fun p ↦ (𝒞 p.2).map
        (fun p'' ↦ (p.1, p''.1, ([RoseTree.node a' p''.2] : 𝓛))))).map projTripleList
      = ((recutRemainder extract (𝒞 cs'')).map projTripleList).map
          (fun z ↦ (z.1, z.2.1,
            ({UnorderedTree.node a' z.2.2} : Multiset (UnorderedTree α)))) := by
  rw [map_projTripleList_recutRemainder, Multiset.map_bind, Multiset.map_bind]
  apply Multiset.bind_congr; intro p _
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; intro p'' _
  exact projTripleList_list_wrap a' p.1 p''.1 p''.2

/-- `recutCrown` distributes over a `cons` outer cut. -/
private theorem recutCrown_cons (F : 𝓕) (l : 𝓛)
    (S : Multiset (𝓕 × 𝓛)) :
    recutCrown extract ((F, l) ::ₘ S)
      = (ℱ F).map (fun c12 ↦ (c12.1, c12.2, l)) + recutCrown extract S := by
  unfold recutCrown; rw [Multiset.cons_bind]

/-- `recutRemainder` distributes over a `cons` outer cut. -/
private theorem recutRemainder_cons (F : 𝓕) (l : 𝓛)
    (S : Multiset (𝓕 × 𝓛)) :
    recutRemainder extract ((F, l) ::ₘ S)
      = (𝒞 l).map (fun q ↦ (F, q.1, q.2)) + recutRemainder extract S := by
  unfold recutRemainder; rw [Multiset.cons_bind]

mutual
/-- For a coherent policy, re-cutting the crowns of the cuts of a list of children enumerates the
same triples as re-cutting their remainders. -/
theorem childrenDoubleCuts_eq (h : ExtractCoherent extract) :
    ∀ cs : 𝓛,
      (recutCrown extract (𝒞 cs)).map projTripleList =
        (recutRemainder extract (𝒞 cs)).map projTripleList
  | [] => by
    rw [childrenCuts_nil]
    unfold recutCrown recutRemainder
    rw [Multiset.singleton_bind, Multiset.singleton_bind, forestCuts_zero, childrenCuts_nil]
    simp only [Multiset.map_singleton]
  | c :: cs' => by
    rw [childrenCuts_cons, recutCrown_conv, recutRemainder_conv, childDoubleCuts_eq h c,
      childrenDoubleCuts_eq h cs']
/-- For a coherent policy, re-cutting the crowns of the cuts at one child enumerates the same
triples as re-cutting their remainders. -/
theorem childDoubleCuts_eq (h : ExtractCoherent extract) :
    ∀ c : RoseTree α,
      (recutCrown extract (childCuts extract c)).map projTripleList =
        (recutRemainder extract (childCuts extract c)).map projTripleList
  | .node a cs => by
    have hchildren := childrenDoubleCuts_eq h cs
    -- Cutting inside the child leaves the policy's verdict on it unchanged.
    have hext (p : 𝓕 × 𝓛) (hp : p ∈ 𝒞 cs) :
        extract (RoseTree.node a p.2) = extract (RoseTree.node a cs) :=
      h.extract_trunk (RoseTree.node a cs) (p.1, RoseTree.node a p.2)
        (by rw [rootCuts_node]; exact Multiset.mem_map.mpr ⟨p, hp, rfl⟩)
    cases hc : extract (RoseTree.node a cs) with
    | none =>
      have hA : childCuts extract (RoseTree.node a cs) =
          (𝒞 cs).map fun p ↦ (p.1, ([RoseTree.node a p.2] : 𝓛)) := by
        rw [childCuts_eq_none _ _ hc, rootCuts_node, Multiset.map_map]; rfl
      have hdcr : recutRemainder extract ((𝒞 cs).map fun p ↦ (p.1, ([RoseTree.node a p.2] : 𝓛))) =
          (𝒞 cs).bind fun p ↦ (𝒞 p.2).map fun p' ↦ (p.1, p'.1, [RoseTree.node a p'.2]) := by
        unfold recutRemainder; rw [Multiset.bind_map]
        refine Multiset.bind_congr fun p hp ↦ ?_
        change (𝒞 [RoseTree.node a p.2]).map (fun q ↦ (p.1, q.1, q.2)) = _
        rw [show 𝒞 [RoseTree.node a p.2] =
              (𝒞 p.2).map fun p' ↦ (p'.1, [RoseTree.node a p'.2]) by
            rw [childrenCuts_singleton, childCuts_eq_none _ _ ((hext p hp).trans hc),
              rootCuts_node, Multiset.map_map]; rfl,
          Multiset.map_map]
        rfl
      rw [hA, recutCrown_node, hdcr, recutRemainder_node, hchildren]
    | some r =>
      have hA : childCuts extract (RoseTree.node a cs) =
          (({RoseTree.node a cs} : 𝓕), r) ::ₘ
            (𝒞 cs).map fun p ↦ (p.1, [RoseTree.node a p.2]) := by
        rw [childCuts_eq_some _ _ _ hc, rootCuts_node, Multiset.map_map]; rfl
      have hdcr : recutRemainder extract ((𝒞 cs).map fun p ↦ (p.1, [RoseTree.node a p.2])) =
          (𝒞 cs).map (fun p ↦ (p.1, ({RoseTree.node a p.2} : 𝓕), r)) +
            (𝒞 cs).bind fun p ↦ (𝒞 p.2).map fun p' ↦ (p.1, p'.1, [RoseTree.node a p'.2]) := by
        rw [← Multiset.bind_cons]
        unfold recutRemainder; rw [Multiset.bind_map]
        refine Multiset.bind_congr fun p hp ↦ ?_
        change (𝒞 [RoseTree.node a p.2]).map (fun q ↦ (p.1, q.1, q.2)) = _
        rw [show 𝒞 [RoseTree.node a p.2] =
              (({RoseTree.node a p.2} : 𝓕), r) ::ₘ
                (𝒞 p.2).map fun p' ↦ (p'.1, [RoseTree.node a p'.2]) by
            rw [childrenCuts_singleton, childCuts_eq_some _ _ _ ((hext p hp).trans hc),
              rootCuts_node, Multiset.map_map]; rfl,
          Multiset.map_cons, Multiset.map_map]
        rfl
      -- Re-cutting the child cut whole gives the full cut and the cuts inside it.
      have hwhole : ((ℱ {RoseTree.node a cs}).map fun c ↦ (c.1, c.2, r)).map projTripleList =
          projTripleList (({RoseTree.node a cs} : 𝓕), (0 : 𝓕), r) ::ₘ
            ((𝒞 cs).map fun p : 𝓕 × 𝓛 ↦
              (p.1, ({RoseTree.node a p.2} : 𝓕), r)).map projTripleList := by
        rw [forestCuts_singleton, treeCuts_node, Multiset.map_cons, Multiset.map_map,
          Multiset.map_cons]
        rfl
      rw [hA, recutCrown_cons, recutRemainder_cons, h.childrenCuts_of_eq_some _ _ hc,
        Multiset.map_singleton, Multiset.map_add, Multiset.map_add, recutCrown_node, hdcr,
        Multiset.map_add, recutRemainder_node, hchildren, hwhole, Multiset.map_singleton]
      simp only [← Multiset.singleton_add]
      abel
end

/-! ### Double cuts of a tree -/

/-- Projecting a `node a`-wrapped triple equals nonplanar-wrapping the
    projected triple. -/
private theorem projTriple_node_wrap (a : α)
    (q : 𝓕 × 𝓕 × 𝓛) :
    projTriple (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕))
      = ((projTripleList q).1, (projTripleList q).2.1,
          ({UnorderedTree.node a (projTripleList q).2.2} : Multiset (UnorderedTree α))) := by
  unfold projTriple projTripleList
  simp only [Multiset.map_singleton]
  rw [UnorderedTree.node_mk_tree_list]

/-- The `node a`-wrap on planar triples, projected, equals the nonplanar
    `node a`-wrap on projected triples. -/
private theorem map_node_wrap_projTriple (a : α)
    (M : Multiset (𝓕 × 𝓕 × 𝓛)) :
    (M.map (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))).map projTriple
      = (M.map projTripleList).map (fun z ↦ (z.1, z.2.1,
          ({UnorderedTree.node a z.2.2} : Multiset (UnorderedTree α)))) := by
  rw [Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl; intro q _
  exact projTriple_node_wrap a q

/-- For a coherent policy, the double cuts of a tree through the crown are its double cuts through
the trunk, up to the order of children. -/
theorem doubleCuts_eq (h : ExtractCoherent extract)
    (t : RoseTree α) :
    (doubleCutsCrown (rootCuts (extract)) t).map projTriple =
      (doubleCutsTrunk (rootCuts (extract)) t).map projTriple := by
  obtain ⟨a, cs⟩ := t
  -- Core: the two genuine remainder re-cuts agree (= `childrenDoubleCuts_eq` wrapped by `node a`).
  have hcore : ((𝒞 cs).bind (fun p ↦ (ℱ p.1).map
        (fun c12 ↦ (c12.1, c12.2, ({RoseTree.node a p.2} : 𝓕))))).map projTriple
      = ((𝒞 cs).bind (fun p ↦ (𝒞 p.2).map
        (fun q ↦ (p.1, q.1, ({RoseTree.node a q.2} : 𝓕))))).map projTriple := by
    rw [show ((𝒞 cs).bind (fun p ↦ (ℱ p.1).map
            (fun c12 ↦ (c12.1, c12.2, ({RoseTree.node a p.2} : 𝓕)))))
          = ((recutCrown extract (𝒞 cs)).map
              (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))) from by
        unfold recutCrown; rw [Multiset.map_bind]
        apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl,
      show ((𝒞 cs).bind (fun p ↦ (𝒞 p.2).map
            (fun q ↦ (p.1, q.1, ({RoseTree.node a q.2} : 𝓕)))))
          = ((recutRemainder extract (𝒞 cs)).map
              (fun q ↦ (q.1, q.2.1, ({RoseTree.node a q.2.2} : 𝓕)))) from by
        unfold recutRemainder; rw [Multiset.map_bind]
        apply Multiset.bind_congr; intro p _; rw [Multiset.map_map]; rfl]
    rw [map_node_wrap_projTriple, map_node_wrap_projTriple, childrenDoubleCuts_eq extract h cs]
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

/-- An enumeration on unordered trees that projects the cuts of a coherent policy has the same
double cuts through the crown as through the trunk. -/
theorem doubleCutsCrown_eq_doubleCutsTrunk
    {cuts : UnorderedTree α → Multiset (Multiset (UnorderedTree α) × UnorderedTree α)}
    (hcuts : ∀ t, cuts (UnorderedTree.mk t) = (rootCuts extract t).map projCut)
    (h : ExtractCoherent extract) (T : UnorderedTree α) :
    doubleCutsCrown cuts T = doubleCutsTrunk cuts T :=
  Quotient.inductionOn T fun t ↦ (doubleCutsCrown_map hcuts t).trans <|
    (doubleCuts_eq extract h t).trans (doubleCutsTrunk_map hcuts t).symm

/-- The policy that leaves nothing is coherent. -/
theorem extractCoherent_leaveNothing : ExtractCoherent (leaveNothing (α := α)) where
  childrenCuts_of_eq_some _ _ h := by
    obtain rfl : [] = _ := Option.some.inj h
    exact childrenCuts_nil _
  extract_trunk _ _ _ := rfl

/-- The admissible cuts have the same double cuts through the crown as through the trunk. -/
theorem doubleCutsCrown_admissibleCuts (T : UnorderedTree α) :
    doubleCutsCrown admissibleCuts T = doubleCutsTrunk admissibleCuts T :=
  doubleCutsCrown_eq_doubleCutsTrunk _ admissibleCuts_mk extractCoherent_leaveNothing T

end ConnesKreimer
