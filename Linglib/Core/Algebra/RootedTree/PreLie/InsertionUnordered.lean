/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.Insertion
public import Linglib.Core.Data.List.Zip
public import Linglib.Core.Data.Multiset.Antidiagonal
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Multi-tree insertion on nonplanar trees

This file defines `UnorderedTree.insertion T G`, the multiset, over all assignments of the guests
`G` to vertices of `T`, of the trees obtained by grafting each guest at its vertex, and
`UnorderedTree.insertionMultiset F G`, the same for a host forest `F`. This is Foissy's formula
for the Guin–Oudom extension of the grafting product. Both are defined by recursion on the host:
grafting into `node a A` places some guests under the root and grafts the rest into the forest
`A`, and grafting into a forest splits the guests among its trees. From it the file defines
`UnorderedTree.productMultiset F G`, the forests of the Grossman–Larson product `F ⋆ G`: over the
splits `G = G₁ + G₂`, the graftings of `G₂` into `F` with `G₁` placed alongside.

## Main results

* `insertion_mk`, `insertionMultiset_mk`: the recursion computes `RoseTree.insertion` and
  `RoseTree.insertionForest` on planar representatives.
* `insertionMultiset_singleton_node`: grafting into a single node `node a A` puts the forests of
  `A ⋆ B` under the root.
* `insertionMultiset_add_host`: grafting into a disjoint union splits the guests between the two
  parts, the rule `AB ∘ C = (A ∘ C₍₁₎)(B ∘ C₍₂₎)` of Oudom and Guin's Proposition 3.7.
* `insertionMultiset_antidiagonal`: splits of an output forest are splits of the host and of the
  guests, each guest following its host.
* `productMultiset_zero_left`, `productMultiset_zero_right`: the empty forest is a unit.
* `productMultiset_bind_antidiagonal`: splits of the forests of `F ⋆ G` are products of splits of
  `F` and of `G`.

## Implementation notes

Grafting into a forest is a `Multiset.foldr` of `insertionStep` over its trees. The fold is well
defined because splitting the guests three ways is symmetric in the first two parts, so no
invariance under reordering of children is needed.

## References

* [foissy-2021]
* [oudom-guin-2008]
-/

@[expose] public section

open RoseTree

private theorem Multiset.bind_antidiagonal_bind_antidiagonal_comm {γ β : Type*} (s : Multiset γ)
    (K : Multiset γ → Multiset γ → Multiset γ → Multiset β) :
    s.antidiagonal.bind (fun p ↦ p.2.antidiagonal.bind fun q ↦ K p.1 q.1 q.2) =
      s.antidiagonal.bind fun p ↦ p.2.antidiagonal.bind fun q ↦ K q.1 p.1 q.2 := by
  induction s using Multiset.induction_on generalizing K with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map, Prod.map_fst,
      Prod.map_snd, id_eq, Multiset.bind_add]
    rw [ih fun x y z ↦ K x y (a ::ₘ z), ih fun x y z ↦ K x (a ::ₘ y) z,
      ih fun x y z ↦ K (a ::ₘ x) y z, add_right_comm]

namespace UnorderedTree

variable {α : Type*}

/-- One step of grafting into a forest. The guests split between a first tree, whose graftings
are `k`, and the remaining trees, whose graftings are `acc`. -/
def insertionStep (k : Multiset (UnorderedTree α) → Multiset (UnorderedTree α))
    (acc : Multiset (UnorderedTree α) → Multiset (Multiset (UnorderedTree α)))
    (G : Multiset (UnorderedTree α)) : Multiset (Multiset (UnorderedTree α)) :=
  G.antidiagonal.bind fun p ↦ (k p.1).bind fun T ↦ (acc p.2).map (T ::ₘ ·)

private theorem insertionStep_insertionStep
    (k k' : Multiset (UnorderedTree α) → Multiset (UnorderedTree α))
    (acc : Multiset (UnorderedTree α) → Multiset (Multiset (UnorderedTree α)))
    (G : Multiset (UnorderedTree α)) :
    insertionStep k (insertionStep k' acc) G = G.antidiagonal.bind fun p ↦ p.2.antidiagonal.bind
      fun q ↦ (k p.1).bind fun T ↦ (k' q.1).bind fun T' ↦ (acc q.2).map (T ::ₘ T' ::ₘ ·) := by
  simp only [insertionStep, Multiset.map_bind, Multiset.map_map, Function.comp_def]
  exact Multiset.bind_congr fun p _ ↦ Multiset.bind_bind _ _

instance : LeftCommutative (insertionStep (α := α)) := ⟨fun k₁ k₂ acc ↦ funext fun G ↦ by
  rw [insertionStep_insertionStep, insertionStep_insertionStep]
  refine (G.bind_antidiagonal_bind_antidiagonal_comm fun x y z ↦ (k₁ x).bind fun T ↦
    (k₂ y).bind fun T' ↦ (acc z).map (T ::ₘ T' ::ₘ ·)).trans ?_
  exact Multiset.bind_congr fun p _ ↦ Multiset.bind_congr fun q _ ↦
    (Multiset.bind_bind _ _).trans <| Multiset.bind_congr fun _ _ ↦ Multiset.bind_congr fun _ _ ↦
      Multiset.map_congr rfl fun _ _ ↦ Multiset.cons_swap _ _ _⟩

/-- `insertion T G` is the multiset, over the assignments of the trees of `G` to vertices of `T`,
of the trees obtained by grafting each guest at its vertex. -/
def insertion : UnorderedTree α → Multiset (UnorderedTree α) → Multiset (UnorderedTree α) :=
  fold fun a ks G ↦ G.antidiagonal.bind fun p ↦
    (ks.foldr insertionStep (fun G ↦ if Multiset.card G = 0 then {0} else 0) p.2).map
      fun X ↦ node a (p.1 + X)

/-- `insertionMultiset F G` is the multiset, over the assignments of the trees of `G` to vertices
of `F`, of the forests obtained by grafting each tree at its vertex. -/
def insertionMultiset (F G : Multiset (UnorderedTree α)) : Multiset (Multiset (UnorderedTree α)) :=
  (F.map insertion).foldr insertionStep (fun G ↦ if Multiset.card G = 0 then {0} else 0) G

theorem insertion_node (a : α) (A G : Multiset (UnorderedTree α)) :
    insertion (node a A) G =
      G.antidiagonal.bind fun p ↦ (insertionMultiset A p.2).map fun X ↦ node a (p.1 + X) := by
  rw [insertion, fold_node]
  rfl

theorem insertionMultiset_zero (G : Multiset (UnorderedTree α)) :
    insertionMultiset 0 G = if Multiset.card G = 0 then {0} else 0 := rfl

theorem insertionMultiset_cons (T : UnorderedTree α) (A G : Multiset (UnorderedTree α)) :
    insertionMultiset (T ::ₘ A) G = G.antidiagonal.bind fun p ↦
      (insertion T p.1).bind fun T' ↦ (insertionMultiset A p.2).map (T' ::ₘ ·) := by
  rw [insertionMultiset, Multiset.map_cons, Multiset.foldr_cons]
  rfl

private theorem antidiagonal_mk (l : List (RoseTree α)) :
    Multiset.antidiagonal (↑(l.map mk) : Multiset (UnorderedTree α)) =
      (↑l.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).map
        fun p => (↑(p.1.map mk), ↑(p.2.map mk)) := by
  rw [Multiset.antidiagonal_coe_sublists', List.sublists'_map, List.revzip_map, List.map_map,
    Multiset.map_coe]
  rfl

private theorem insertionMultiset_mk_of {hs : List (RoseTree α)}
    (ih : ∀ h ∈ hs, ∀ gs : List (RoseTree α),
      insertion (mk h) ↑(gs.map mk) = (RoseTree.insertion h gs).map mk) (gs : List (RoseTree α)) :
    insertionMultiset ↑(hs.map mk) ↑(gs.map mk) =
      (insertionForest hs gs).map fun L => (↑(L.map mk) : Multiset (UnorderedTree α)) := by
  induction hs generalizing gs with
  | nil => cases gs <;> simp [insertionMultiset_zero]
  | cons h hs ihs =>
    rw [List.map_cons, ← Multiset.cons_coe, insertionMultiset_cons, insertionForest_cons_msform,
      antidiagonal_mk, Multiset.bind_map]
    refine Multiset.bind_congr fun p _ ↦ ?_
    rw [ih h List.mem_cons_self, ihs fun h hh ↦ ih h (List.mem_cons_of_mem _ hh)]

/-- `insertion` computes `RoseTree.insertion` on planar representatives. -/
theorem insertion_mk (t : RoseTree α) (gs : List (RoseTree α)) :
    insertion (mk t) ↑(gs.map mk) = (RoseTree.insertion t gs).map mk := by
  induction t generalizing gs with
  | node a cs ih =>
    rw [← node_mk_tree_list, insertion_node, insertion_node_msform, antidiagonal_mk,
      Multiset.bind_map]
    exact Multiset.bind_congr fun p _ ↦ by rw [insertionMultiset_mk_of ih]

/-- `insertionMultiset` computes `RoseTree.insertionForest` on planar representatives. -/
theorem insertionMultiset_mk (hs gs : List (RoseTree α)) :
    insertionMultiset ↑(hs.map mk) ↑(gs.map mk) =
      (insertionForest hs gs).map fun L => (↑(L.map mk) : Multiset (UnorderedTree α)) :=
  insertionMultiset_mk_of (fun h _ ↦ insertion_mk h) gs

theorem insertionMultiset_zero_right (F : Multiset (UnorderedTree α)) :
    insertionMultiset F 0 = {F} := by
  induction F using forest_inductionOn with
  | h hs =>
    have h := insertionMultiset_mk hs []
    rwa [insertionForest_nil_guests, Multiset.map_singleton] at h

theorem insertionMultiset_zero_left_of_ne_zero (G : Multiset (UnorderedTree α)) (h : G ≠ 0) :
    insertionMultiset 0 G = 0 := by
  simp [insertionMultiset_zero, h]

theorem insertionMultiset_singleton (T : UnorderedTree α) (G : Multiset (UnorderedTree α)) :
    insertionMultiset {T} G = (insertion T G).map ({·}) := by
  induction T using Quotient.inductionOn with | h t =>
  induction G using forest_inductionOn with | h gs =>
  rw [quot_mk_eq_mk, ← Multiset.coe_singleton, ← List.map_singleton, insertionMultiset_mk,
    insertionForest_singleton, insertion_mk, Multiset.map_map, Multiset.map_map]
  rfl

theorem insertionMultiset_card_eq (A B : Multiset (UnorderedTree α))
    {F : Multiset (UnorderedTree α)} (h : F ∈ insertionMultiset A B) : F.card = A.card := by
  induction A using forest_inductionOn with | h hs =>
  induction B using forest_inductionOn with | h gs =>
  rw [insertionMultiset_mk, Multiset.mem_map] at h
  obtain ⟨L, hL, rfl⟩ := h
  simp [length_of_mem_insertionForest hL]

theorem insertionMultiset_singleton_value (T : UnorderedTree α) (B : Multiset (UnorderedTree α))
    {F : Multiset (UnorderedTree α)} (h : F ∈ insertionMultiset {T} B) :
    ∃ T', F = {T'} ∧ T'.value = T.value := by
  induction T using Quotient.inductionOn with | h t =>
  induction B using forest_inductionOn with | h gs =>
  rw [quot_mk_eq_mk, ← Multiset.coe_singleton, ← List.map_singleton, insertionMultiset_mk,
    insertionForest_singleton, Multiset.map_map, Multiset.mem_map] at h
  obtain ⟨T', hT', rfl⟩ := h
  exact ⟨mk T', rfl, value_of_mem_insertion hT'⟩

/-- Grafting into `A` gives a single tree with root `a` only if `A` is one. -/
theorem exists_eq_singleton_node_of_mem_insertionMultiset {a : α}
    {A B G : Multiset (UnorderedTree α)} (h : {node a G} ∈ insertionMultiset A B) :
    ∃ F, A = {node a F} := by
  obtain ⟨T, rfl⟩ := Multiset.card_eq_one.mp
    ((insertionMultiset_card_eq A B h).symm.trans (Multiset.card_singleton _))
  obtain ⟨T', hT', hv⟩ := insertionMultiset_singleton_value T B h
  rw [← Multiset.singleton_inj.mp hT', value_node] at hv
  exact ⟨T.children, by rw [hv, node_eta]⟩

/-- Splits of an output forest are splits of the host and of the guests, each guest following
its host. -/
theorem insertionMultiset_antidiagonal (A G : Multiset (UnorderedTree α)) :
    (insertionMultiset A G).bind Multiset.antidiagonal =
      A.antidiagonal.bind fun pa => G.antidiagonal.bind fun pg =>
        insertionMultiset pa.1 pg.1 ×ˢ insertionMultiset pa.2 pg.2 := by
  induction A using forest_inductionOn with | h hs =>
  induction G using forest_inductionOn with | h gs =>
  have hL (L : List (RoseTree α)) : Multiset.antidiagonal (↑(L.map mk) : Multiset _) =
      (↑L.sublists'.revzip : Multiset (List (RoseTree α) × List (RoseTree α))).bind fun x =>
        {((↑(x.1.map mk) : Multiset (UnorderedTree α)), ↑(x.2.map mk))} := by
    rw [antidiagonal_mk, Multiset.bind_singleton]
  rw [antidiagonal_mk, antidiagonal_mk, Multiset.bind_map, insertionMultiset_mk, Multiset.bind_map]
  simp only [hL]
  rw [insertionForest_bind_revzip_sublists' hs gs fun L₁ L₂ =>
    {((↑(L₁.map mk) : Multiset (UnorderedTree α)), (↑(L₂.map mk) : Multiset (UnorderedTree α)))}]
  refine Multiset.bind_congr fun h _ => ?_
  rw [Multiset.bind_map]
  refine Multiset.bind_congr fun q _ => ?_
  rw [insertionMultiset_mk, insertionMultiset_mk, Multiset.bind_bind]
  simp only [SProd.sprod, Multiset.product, Multiset.bind_map, Multiset.map_map]
  exact Multiset.bind_congr fun L₁ _ => Multiset.bind_singleton _ _

/-- Grafting into a disjoint union splits the guests between the two parts. -/
theorem insertionMultiset_add_host (A B C : Multiset (UnorderedTree α)) :
    insertionMultiset (A + B) C =
      C.antidiagonal.bind fun p =>
        (insertionMultiset A p.1 ×ˢ insertionMultiset B p.2).map fun q => q.1 + q.2 := by
  induction A using forest_inductionOn with | h as =>
  induction B using forest_inductionOn with | h bs =>
  induction C using forest_inductionOn with | h cs =>
  rw [Multiset.coe_add, ← List.map_append, insertionMultiset_mk, insertionForest_append,
    Multiset.map_bind, antidiagonal_mk, Multiset.bind_map]
  refine Multiset.bind_congr fun p _ => ?_
  rw [insertionMultiset_mk, insertionMultiset_mk]
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.bind_map, Multiset.map_map]
  exact Multiset.bind_congr fun L₁ _ => Multiset.map_congr rfl fun L₂ _ => by simp

/-! ### The Grossman–Larson product -/

/-- `productMultiset F G` is the multiset of forests in the Grossman–Larson product `F ⋆ G`: over
the splits `G = G₁ + G₂`, the forests `X + G₁` with `X` a grafting of the trees of `G₂` onto `F`. -/
def productMultiset (F G : Multiset (UnorderedTree α)) :
    Multiset (Multiset (UnorderedTree α)) :=
  G.antidiagonal.bind fun p ↦ (insertionMultiset F p.2).map (· + p.1)

@[simp] theorem productMultiset_zero_right (F : Multiset (UnorderedTree α)) :
    productMultiset F 0 = {F} := by
  simp [productMultiset, insertionMultiset_zero_right]

@[simp] theorem productMultiset_zero_left (G : Multiset (UnorderedTree α)) :
    productMultiset 0 G = {G} := by
  induction G using Multiset.induction with
  | empty => simp [productMultiset, insertionMultiset_zero_right]
  | cons a G ih =>
    rw [productMultiset] at ih ⊢
    rw [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map, Multiset.bind_map]
    have h (p : Multiset (UnorderedTree α) × Multiset (UnorderedTree α)) :
        (insertionMultiset 0 (a ::ₘ p.2)).map (· + p.1) = 0 := by
      rw [insertionMultiset_zero_left_of_ne_zero _ (Multiset.cons_ne_zero), Multiset.map_zero]
    simp only [Prod.map_fst, Prod.map_snd, id_eq, h, Multiset.bind_zero, zero_add]
    simpa [Multiset.map_bind, Multiset.map_map, Function.comp_def] using
      congrArg (Multiset.map (a ::ₘ ·)) ih

theorem card_le_of_mem_productMultiset {F G W : Multiset (UnorderedTree α)}
    (h : W ∈ productMultiset F G) : F.card ≤ W.card := by
  obtain ⟨p, -, h⟩ := Multiset.mem_bind.mp h
  obtain ⟨X, hX, rfl⟩ := Multiset.mem_map.mp h
  simp [insertionMultiset_card_eq F p.2 hX]

/-- Grafting into a single node `node a A` puts the forests of `A ⋆ B` under the root: each guest
is a new child of the root or grafted into `A`. -/
theorem insertionMultiset_singleton_node (a : α) (A B : Multiset (UnorderedTree α)) :
    insertionMultiset {node a A} B = (productMultiset A B).map fun F => {node a F} := by
  rw [insertionMultiset_singleton, insertion_node, productMultiset, Multiset.map_bind,
    Multiset.map_bind]
  exact Multiset.bind_congr fun p _ ↦ by simp only [Multiset.map_map, Function.comp_def, add_comm]

/-! ### Splits of a product

Splitting the forests of `F ⋆ G` is splitting `F` and `G` and multiplying the parts. This is the
multiset form of the compatibility between the Grossman–Larson product and the coproduct of the
symmetric algebra, Oudom and Guin's Lemma 3.11. -/

private theorem product_bind {β γ δ : Type*} (s : Multiset β) (t : Multiset γ)
    (F : β × γ → Multiset δ) :
    (s ×ˢ t).bind F = s.bind (fun a => t.bind (fun b => F (a, b))) := by
  simp [SProd.sprod, Multiset.product, Multiset.bind_assoc, Multiset.bind_map]

private theorem bind_product_left {β γ δ : Type*} (s : Multiset β)
    (f : β → Multiset γ) (t : Multiset δ) :
    (s.bind f) ×ˢ t = s.bind (fun a => f a ×ˢ t) := by
  simp [SProd.sprod, Multiset.product, Multiset.bind_assoc]

private theorem product_bind_right {β γ δ : Type*} (s : Multiset β)
    (t : Multiset γ) (g : γ → Multiset δ) :
    s ×ˢ (t.bind g) = t.bind (fun b => s ×ˢ g b) := by
  simp [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.bind_bind s t]

private theorem map_product_map {β γ β' γ' : Type*} (s : Multiset β) (t : Multiset γ)
    (f : β → β') (g : γ → γ') :
    (s.map f) ×ˢ (t.map g) = (s ×ˢ t).map (Prod.map f g) := by
  simp [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.bind_map, Multiset.map_map]

private theorem bind_antidiagonal_middle_swap {β γ : Type*} (B : Multiset β)
    (g : Multiset β → Multiset β → Multiset β → Multiset β → Multiset γ) :
    B.antidiagonal.bind (fun p ↦ p.1.antidiagonal.bind fun u ↦ p.2.antidiagonal.bind fun v ↦
        g u.1 u.2 v.1 v.2) =
      B.antidiagonal.bind fun p ↦ p.1.antidiagonal.bind fun u ↦ p.2.antidiagonal.bind fun v ↦
        g u.1 v.1 u.2 v.2 := by
  induction B using Multiset.induction_on generalizing g with
  | empty => simp
  | cons a B ih =>
    simp only [Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map, Prod.map_fst,
      Prod.map_snd, id_eq, Multiset.bind_add]
    rw [ih fun x y z w ↦ g x y z (a ::ₘ w), ih fun x y z w ↦ g x y (a ::ₘ z) w,
      ih fun x y z w ↦ g x (a ::ₘ y) z w, ih fun x y z w ↦ g (a ::ₘ x) y z w]
    abel

/-- Splitting the forests of `A ⋆ B` is splitting `A` and `B` and multiplying the parts. -/
theorem productMultiset_bind_antidiagonal (A B : Multiset (UnorderedTree α)) :
    (productMultiset A B).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A ×ˢ Multiset.antidiagonal B).bind (fun pq =>
        productMultiset pq.1.1 pq.2.1 ×ˢ productMultiset pq.1.2 pq.2.2) := by
  -- Split each output forest `X + p.1` as a split of `X` plus a split of `p.1`.
  have stepACD : ∀ p ∈ Multiset.antidiagonal B,
      ((insertionMultiset A p.2).map (· + p.1)).bind Multiset.antidiagonal =
      (Multiset.antidiagonal A).bind (fun pa =>
        (Multiset.antidiagonal p.2).bind (fun pH =>
          (Multiset.antidiagonal p.1).bind (fun q =>
            (insertionMultiset pa.1 pH.1 ×ˢ
              insertionMultiset pa.2 pH.2).map
              (fun pX => (pX.1 + q.1, pX.2 + q.2))))) := by
    intro p _
    have h1 : ((insertionMultiset A p.2).map (· + p.1)).bind
          Multiset.antidiagonal =
        ((insertionMultiset A p.2).bind Multiset.antidiagonal).bind
          (fun r => (Multiset.antidiagonal p.1).map
            (fun q => (r.1 + q.1, r.2 + q.2))) := by
      rw [Multiset.bind_map, Multiset.bind_assoc]
      exact Multiset.bind_congr fun X _ => Multiset.antidiagonal_add X p.1
    rw [h1, insertionMultiset_antidiagonal, Multiset.bind_assoc]
    refine Multiset.bind_congr fun pa _ => ?_
    rw [Multiset.bind_assoc]
    refine Multiset.bind_congr fun pH _ => ?_
    exact Multiset.bind_map_comm _ _
  rw [productMultiset, Multiset.bind_assoc, Multiset.bind_congr stepACD, Multiset.bind_bind,
    product_bind]
  refine Multiset.bind_congr fun pa _ => ?_
  rw [Multiset.bind_congr fun pb _ => Multiset.bind_bind _ _,
    bind_antidiagonal_middle_swap B fun a b c d =>
      (insertionMultiset pa.1 c ×ˢ insertionMultiset pa.2 d).map fun pX => (pX.1 + a, pX.2 + b)]
  refine Multiset.bind_congr fun pb _ => ?_
  rw [productMultiset, productMultiset, bind_product_left]
  refine Multiset.bind_congr fun u _ => ?_
  rw [product_bind_right]
  refine Multiset.bind_congr fun v _ => ?_
  rw [map_product_map]
  rfl

end UnorderedTree
