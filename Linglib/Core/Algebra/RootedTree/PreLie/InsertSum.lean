/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.RootedTree.PreLie.InsertionUnordered

/-!
# The grafting pre-Lie product on rooted trees

The grafting product `T ◁ S` of two rooted trees is the multiset of the trees obtained by
grafting `S` onto one vertex of `T`, that is, by making `S` a new child of that vertex. It has
one summand for each vertex of `T` (`RoseTree.insertSum_eq_map_graft`), the new child at the root
or inside one child (`RoseTree.insertSum_node`), and is the one-guest case of the multi-insertion
`insertion T gs`, which grafts every guest of `gs` at once. On nonplanar trees, grafting `S₁` and
then `S₂` is grafting `S₁ ◁ S₂`, plus grafting both at once
(`UnorderedTree.insertSum_bind_insertSum`), so the associator is symmetric in its last two
arguments (`UnorderedTree.insertSum_assoc_symm`). This is the right pre-Lie identity, by which
Chapoton and Livernet make the rooted trees a pre-Lie algebra.

## Implementation notes

The pre-Lie identity holds only once children are unordered: grafting `S₁` and then `S₂` at one
vertex makes the new children `[S₂, S₁]`, where grafting both at once makes them `[S₁, S₂]`.

## References

* [chapoton-livernet-2001]
* [foissy-2021]
* [oudom-guin-2008]
-/

@[expose] public section

namespace RoseTree

variable {α : Type*}

/-- The grafting product `T ◁ S` is the multiset of trees obtained by grafting `S` as a new
first child of one vertex of `T`. -/
def insertSum (T S : RoseTree α) : Multiset (RoseTree α) :=
  insertion T [S]

@[inherit_doc] scoped infixl:65 " ◁ " => insertSum

/-- `T ◁ S` sums, over the vertices `p` of `T`, the grafting of `S` at `p`. -/
theorem insertSum_eq_map_graft (T S : RoseTree α) :
    T ◁ S = ((vertices T).map fun p ↦ graft T (Function.update (fun _ ↦ []) p [S]) :
      Multiset (RoseTree α)) := by
  rw [insertSum, insertion_def, List.length_singleton, List.replicate_one, List.sections_singleton,
    List.map_map]
  refine congrArg _ (List.map_congr_left fun p _ ↦ congrArg _ (funext fun q ↦ ?_))
  by_cases h : p = q <;> simp [h, eq_comm]

/-- Grafting into a node either adds a child at the root or grafts inside the children. -/
theorem insertSum_node (a : α) (cs : List (RoseTree α)) (S : RoseTree α) :
    node a cs ◁ S = node a (S :: cs) ::ₘ (insertionForest cs [S]).map (node a) := by
  rw [insertSum, insertion_node, show [S].sublists'.revzip = [([], [S]), ([S], [])] from rfl,
    ← Multiset.cons_coe, Multiset.cons_bind, Multiset.coe_singleton, Multiset.singleton_bind,
    insertionForest_nil_guests, Multiset.map_singleton, add_comm, Multiset.singleton_add]
  rfl

@[simp] theorem insertSum_leaf (a : α) (S : RoseTree α) : leaf a ◁ S = {node a [S]} := by
  rw [insertSum_node, insertionForest_empty_host_nonempty_guests, Multiset.map_zero]
  rfl

theorem card_insertSum (T S : RoseTree α) : Multiset.card (T ◁ S) = T.numNodes := by
  rw [insertSum_eq_map_graft, Multiset.coe_card, List.length_map, length_vertices]

/-- Grafting a leaf onto a two-vertex path adds it at the root or at the old leaf. -/
example : node 0 [leaf 1] ◁ leaf 2 = {node 0 [leaf 2, leaf 1], node 0 [node 1 [leaf 2]]} := by
  decide

/-- Every summand of `T ◁ S` has the vertices of `T` and those of `S`. -/
theorem numNodes_of_mem_insertSum {T S X : RoseTree α} (h : X ∈ T ◁ S) :
    X.numNodes = T.numNodes + S.numNodes := by
  rw [insertSum_eq_map_graft, Multiset.mem_coe, List.mem_map] at h
  obtain ⟨p, hp, rfl⟩ := h
  rw [numNodes_graft, List.sum_map_eq_nsmul_single p _ fun q hq _ ↦ by simp [hq],
    @List.count_eq_one_of_mem _ instBEqOfDecidableEq _ _ _ (nodup_vertices T) hp]
  simp

/-- Grafting is not associative, since `(0 ◁ 1) ◁ 2` has two summands and `0 ◁ (1 ◁ 2)` one. -/
example : (leaf 0 ◁ leaf 1).bind (· ◁ leaf 2) ≠ (leaf 1 ◁ leaf 2).bind (leaf 0 ◁ ·) := by
  decide

end RoseTree

namespace UnorderedTree

variable {α : Type*}

/-- The grafting product on nonplanar trees, the insertion of a single guest. -/
def insertSum (T S : UnorderedTree α) : Multiset (UnorderedTree α) :=
  insertion T {S}

@[inherit_doc] scoped infixl:65 " ◁ " => UnorderedTree.insertSum

@[simp] theorem mk_insertSum (T S : RoseTree α) :
    mk T ◁ mk S = (RoseTree.insertSum T S).map mk :=
  insertion_mk T [S]

theorem card_insertSum (T S : UnorderedTree α) : Multiset.card (T ◁ S) = T.numNodes :=
  Quotient.inductionOn₂ T S fun t s => by
    change Multiset.card (mk t ◁ mk s) = (mk t).numNodes
    rw [mk_insertSum, Multiset.card_map, RoseTree.card_insertSum, numNodes_mk]

/-- Grafting into a node either adds a child at the root or grafts inside the children. -/
theorem insertSum_node (a : α) (F : Multiset (UnorderedTree α)) (S : UnorderedTree α) :
    node a F ◁ S = node a (S ::ₘ F) ::ₘ (insertionMultiset F {S}).map (node a) := by
  rw [insertSum, insertion_node, ← Multiset.cons_zero, Multiset.antidiagonal_cons,
    Multiset.antidiagonal_zero]
  simp only [insertionMultiset_zero_right, add_comm, Multiset.map_singleton, Prod.map_apply, id,
    Multiset.cons_bind, Multiset.singleton_bind, Multiset.cons_zero, Multiset.singleton_add,
    add_zero]
  rw [add_comm, Multiset.singleton_add, add_comm F, Multiset.singleton_add]

/-- Every summand of `T ◁ S` has the vertices of `T` and those of `S`. -/
theorem numNodes_of_mem_insertSum {T S X : UnorderedTree α} (h : X ∈ T ◁ S) :
    X.numNodes = T.numNodes + S.numNodes := by
  induction T using Quotient.inductionOn with | h t =>
  induction S using Quotient.inductionOn with | h s =>
  rw [quot_mk_eq_mk, quot_mk_eq_mk, mk_insertSum, Multiset.mem_map] at h
  obtain ⟨x, hx, rfl⟩ := h
  rw [numNodes_mk, RoseTree.numNodes_of_mem_insertSum hx]
  rfl

theorem insertion_zero (T : UnorderedTree α) : insertion T 0 = {T} := by
  induction T using Quotient.inductionOn with | h t =>
  exact (insertion_mk t []).trans
    (by rw [RoseTree.insertion_nil_guests, Multiset.map_singleton]; rfl)

/-- Grafting into a forest grafts into its first tree or into the rest. -/
theorem insertionMultiset_cons_singleton (T : UnorderedTree α) (F : Multiset (UnorderedTree α))
    (S : UnorderedTree α) :
    insertionMultiset (T ::ₘ F) {S} =
      (T ◁ S).map (· ::ₘ F) + (insertionMultiset F {S}).map (T ::ₘ ·) := by
  rw [insertionMultiset_cons, ← Multiset.cons_zero S, Multiset.antidiagonal_cons,
    Multiset.antidiagonal_zero]
  simp only [insertionMultiset_zero_right, insertion_zero, Multiset.map_singleton, Prod.map_apply,
    id, Multiset.cons_bind, Multiset.singleton_bind, Multiset.cons_zero, Multiset.singleton_add,
    Multiset.bind_singleton, insertSum]
  exact add_comm _ _

theorem insertionMultiset_singleton_singleton (T S : UnorderedTree α) :
    insertionMultiset {T} {S} = (T ◁ S).map ({·}) :=
  insertionMultiset_singleton T {S}

theorem productMultiset_singleton_singleton (T S : UnorderedTree α) :
    productMultiset {T} {S} = {T, S} ::ₘ (T ◁ S).map ({·}) := by
  rw [productMultiset, ← Multiset.cons_zero, Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
  simp [insertionMultiset_zero_right, insertionMultiset_singleton_singleton, add_comm]

/-! ### Grafting one more tree

Grafting a tree `X` onto a forest that already carries the guests `G` either grafts it onto the
host, as one more guest, or onto one of the guests. -/

private theorem insertionMultiset_add_singleton (P L : Multiset (UnorderedTree α))
    (X : UnorderedTree α) :
    insertionMultiset (P + L) {X} =
      (insertionMultiset P {X}).map (· + L) + (insertionMultiset L {X}).map (P + ·) := by
  induction P using Multiset.induction_on with
  | empty => simp [insertionMultiset_zero_left_of_ne_zero]
  | cons T P ih =>
    simp only [Multiset.cons_add, insertionMultiset_cons_singleton, ih, Multiset.map_add,
      Multiset.map_map, Function.comp_def, add_assoc]

private theorem bind_antidiagonal_insertionMultiset_singleton (G : Multiset (UnorderedTree α))
    (X : UnorderedTree α) :
    (insertionMultiset G {X}).bind Multiset.antidiagonal =
      G.antidiagonal.bind fun p ↦
        (insertionMultiset p.1 {X}).map (·, p.2) + (insertionMultiset p.2 {X}).map (p.1, ·) := by
  rw [insertionMultiset_antidiagonal]
  refine Multiset.bind_congr fun p _ ↦ ?_
  rw [← Multiset.cons_zero X, Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
  simp [SProd.sprod, Multiset.product, insertionMultiset_zero_right, add_comm]

private theorem insertionMultiset_bind_singleton_of {F : Multiset (UnorderedTree α)}
    {X : UnorderedTree α}
    (h : ∀ T ∈ F, ∀ G, (insertion T G).bind (· ◁ X) =
      insertion T (X ::ₘ G) + (insertionMultiset G {X}).bind (insertion T ·))
    (G : Multiset (UnorderedTree α)) :
    (insertionMultiset F G).bind (insertionMultiset · {X}) =
      insertionMultiset F (X ::ₘ G) + (insertionMultiset G {X}).bind (insertionMultiset F ·) := by
  induction F using Multiset.induction_on generalizing G with
  | empty =>
    have h0 : (insertionMultiset G {X}).bind (insertionMultiset 0 ·) = 0 := by
      refine (Multiset.bind_congr fun G' hG' ↦
        insertionMultiset_zero_left_of_ne_zero G' ?_).trans (Multiset.bind_zero _)
      rintro rfl
      obtain rfl := Multiset.card_eq_zero.mp (insertionMultiset_card_eq G {X} hG').symm
      simp [insertionMultiset_zero_left_of_ne_zero] at hG'
    rw [h0, insertionMultiset_zero_left_of_ne_zero _ (Multiset.cons_ne_zero), add_zero]
    by_cases hG : G = 0
    · simp [hG, insertionMultiset_zero_right, insertionMultiset_zero_left_of_ne_zero]
    · rw [insertionMultiset_zero_left_of_ne_zero _ hG, Multiset.zero_bind]
  | cons T A ihA =>
    have hT := h T (Multiset.mem_cons_self T A)
    have hA := fun G ↦ ihA (fun T' hT' ↦ h T' (Multiset.mem_cons_of_mem hT')) G
    have hL : (insertionMultiset (T ::ₘ A) G).bind (insertionMultiset · {X}) =
        G.antidiagonal.bind fun p ↦
          (((insertion T p.1).bind (· ◁ X)).bind fun T' ↦
            (insertionMultiset A p.2).map (T' ::ₘ ·)) +
          (insertion T p.1).bind fun T' ↦
            ((insertionMultiset A p.2).bind (insertionMultiset · {X})).map (T' ::ₘ ·) := by
      rw [insertionMultiset_cons, Multiset.bind_assoc]
      refine Multiset.bind_congr fun p _ ↦ ?_
      simp only [Multiset.bind_assoc, Multiset.bind_map, insertionMultiset_cons_singleton,
        Multiset.bind_add, Multiset.map_bind]
      congr 1
      exact Multiset.bind_congr fun T' _ ↦ Multiset.bind_map_comm _ _
    have hR1 : insertionMultiset (T ::ₘ A) (X ::ₘ G) =
        (G.antidiagonal.bind fun p ↦ (insertion T p.1).bind fun T' ↦
          (insertionMultiset A (X ::ₘ p.2)).map (T' ::ₘ ·)) +
        G.antidiagonal.bind fun p ↦ (insertion T (X ::ₘ p.1)).bind fun T' ↦
          (insertionMultiset A p.2).map (T' ::ₘ ·) := by
      rw [insertionMultiset_cons, Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
        Multiset.bind_map]
      rfl
    have hR2 : (insertionMultiset G {X}).bind (insertionMultiset (T ::ₘ A) ·) =
        (G.antidiagonal.bind fun p ↦ (insertionMultiset p.1 {X}).bind fun P ↦
          (insertion T P).bind fun T' ↦ (insertionMultiset A p.2).map (T' ::ₘ ·)) +
        G.antidiagonal.bind fun p ↦ (insertionMultiset p.2 {X}).bind fun P ↦
          (insertion T p.1).bind fun T' ↦ (insertionMultiset A P).map (T' ::ₘ ·) := by
      simp only [insertionMultiset_cons]
      rw [← Multiset.bind_assoc, bind_antidiagonal_insertionMultiset_singleton,
        Multiset.bind_assoc, ← Multiset.bind_add]
      refine Multiset.bind_congr fun p _ ↦ ?_
      rw [Multiset.add_bind, Multiset.bind_map, Multiset.bind_map]
    have hd : (G.antidiagonal.bind fun p ↦ (insertion T p.1).bind fun T' ↦
          (insertionMultiset p.2 {X}).bind fun P ↦ (insertionMultiset A P).map (T' ::ₘ ·)) =
        G.antidiagonal.bind fun p ↦ (insertionMultiset p.2 {X}).bind fun P ↦
          (insertion T p.1).bind fun T' ↦ (insertionMultiset A P).map (T' ::ₘ ·) :=
      Multiset.bind_congr fun p _ ↦ Multiset.bind_bind _ _
    rw [hL]
    simp only [hT, hA]
    rw [hR1, hR2]
    simp only [Multiset.add_bind, Multiset.bind_assoc, Multiset.map_add, Multiset.bind_add,
      Multiset.map_bind]
    rw [hd]
    abel

/-- Grafting `X` onto a tree that carries the guests `G` grafts `X` onto the host as one more
guest, or onto one of the guests. -/
theorem insertion_bind_insertSum (T : UnorderedTree α) (G : Multiset (UnorderedTree α))
    (X : UnorderedTree α) :
    (insertion T G).bind (· ◁ X) =
      insertion T (X ::ₘ G) + (insertionMultiset G {X}).bind (insertion T ·) := by
  induction T generalizing G with
  | node a A ih =>
    have hA := fun G ↦ insertionMultiset_bind_singleton_of (F := A) (X := X) ih G
    have hL : (insertion (node a A) G).bind (· ◁ X) =
        G.antidiagonal.bind fun p ↦
          (insertionMultiset A p.2).map (fun L ↦ node a (X ::ₘ (p.1 + L))) +
          ((insertionMultiset p.1 {X}).bind fun P ↦
            (insertionMultiset A p.2).map fun L ↦ node a (P + L)) +
          ((insertionMultiset A p.2).bind (insertionMultiset · {X})).map
            fun L ↦ node a (p.1 + L) := by
      rw [insertion_node, Multiset.bind_assoc]
      refine Multiset.bind_congr fun p _ ↦ ?_
      simp only [Multiset.bind_map, insertSum_node, insertionMultiset_add_singleton,
        Multiset.bind_cons, Multiset.map_add, Multiset.map_map, Multiset.bind_add,
        Multiset.map_bind, Function.comp_def, add_assoc]
      congr 2
      exact Multiset.bind_map_comm _ _
    have hR1 : insertion (node a A) (X ::ₘ G) =
        (G.antidiagonal.bind fun p ↦
          (insertionMultiset A (X ::ₘ p.2)).map fun L ↦ node a (p.1 + L)) +
        G.antidiagonal.bind fun p ↦
          (insertionMultiset A p.2).map fun L ↦ node a (X ::ₘ (p.1 + L)) := by
      rw [insertion_node, Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
        Multiset.bind_map]
      simp only [Prod.map_fst, Prod.map_snd, id, Multiset.cons_add]
    have hR2 : (insertionMultiset G {X}).bind (insertion (node a A) ·) =
        (G.antidiagonal.bind fun p ↦ (insertionMultiset p.1 {X}).bind fun P ↦
          (insertionMultiset A p.2).map fun L ↦ node a (P + L)) +
        G.antidiagonal.bind fun p ↦ (insertionMultiset p.2 {X}).bind fun P ↦
          (insertionMultiset A P).map fun L ↦ node a (p.1 + L) := by
      simp only [insertion_node]
      rw [← Multiset.bind_assoc, bind_antidiagonal_insertionMultiset_singleton,
        Multiset.bind_assoc, ← Multiset.bind_add]
      refine Multiset.bind_congr fun p _ ↦ ?_
      rw [Multiset.add_bind, Multiset.bind_map, Multiset.bind_map]
    rw [hL]
    simp only [hA]
    rw [hR1, hR2]
    simp only [Multiset.map_add, Multiset.bind_add, Multiset.map_bind]
    abel

/-- Grafting `X` onto a forest that carries the guests `G` grafts `X` onto the host as one more
guest, or onto one of the guests: the rule `(F ∘ G) ∘ X = F ∘ (G X) + F ∘ (G ∘ X)` of
[oudom-guin-2008]. -/
theorem insertionMultiset_bind_singleton (F G : Multiset (UnorderedTree α))
    (X : UnorderedTree α) :
    (insertionMultiset F G).bind (insertionMultiset · {X}) =
      insertionMultiset F (X ::ₘ G) + (insertionMultiset G {X}).bind (insertionMultiset F ·) :=
  insertionMultiset_bind_singleton_of (fun T _ G ↦ insertion_bind_insertSum T G X) G

theorem productMultiset_singleton (W : Multiset (UnorderedTree α)) (X : UnorderedTree α) :
    productMultiset W {X} = (X ::ₘ W) ::ₘ insertionMultiset W {X} := by
  rw [productMultiset, ← Multiset.cons_zero, Multiset.antidiagonal_cons, Multiset.antidiagonal_zero]
  simp [insertionMultiset_zero_right, add_comm]
  rw [add_comm, Multiset.singleton_add]

/-- Multiplying by one more tree `X` on the right, after the forest `E`, multiplies by `X` and
`E` together or by `E` with `X` grafted onto it. -/
theorem productMultiset_bind_singleton (F E : Multiset (UnorderedTree α)) (X : UnorderedTree α) :
    (productMultiset F E).bind (productMultiset · {X}) =
      productMultiset F (X ::ₘ E) + (insertionMultiset E {X}).bind (productMultiset F ·) := by
  have hL : (productMultiset F E).bind (productMultiset · {X}) =
      E.antidiagonal.bind fun p ↦
        (insertionMultiset F p.2).map (fun Y ↦ X ::ₘ (Y + p.1)) +
        ((insertionMultiset F p.2).bind (insertionMultiset · {X})).map (· + p.1) +
        (insertionMultiset p.1 {X}).bind fun P ↦ (insertionMultiset F p.2).map (· + P) := by
    rw [productMultiset, Multiset.bind_assoc]
    refine Multiset.bind_congr fun p _ ↦ ?_
    simp only [Multiset.bind_map, productMultiset_singleton, insertionMultiset_add_singleton,
      Multiset.bind_cons, Multiset.map_map, Multiset.bind_add,
      Multiset.map_bind, Function.comp_def, add_assoc]
    congr 2
    exact Multiset.bind_map_comm _ _
  have hR1 : productMultiset F (X ::ₘ E) =
      (E.antidiagonal.bind fun p ↦ (insertionMultiset F (X ::ₘ p.2)).map (· + p.1)) +
      E.antidiagonal.bind fun p ↦ (insertionMultiset F p.2).map fun Y ↦ X ::ₘ (Y + p.1) := by
    rw [productMultiset, Multiset.antidiagonal_cons, Multiset.add_bind, Multiset.bind_map,
      Multiset.bind_map]
    simp only [Prod.map_fst, Prod.map_snd, id, Multiset.add_cons]
  have hR2 : (insertionMultiset E {X}).bind (productMultiset F ·) =
      (E.antidiagonal.bind fun p ↦ (insertionMultiset p.1 {X}).bind fun P ↦
        (insertionMultiset F p.2).map (· + P)) +
      E.antidiagonal.bind fun p ↦ (insertionMultiset p.2 {X}).bind fun P ↦
        (insertionMultiset F P).map (· + p.1) := by
    simp only [productMultiset]
    rw [← Multiset.bind_assoc, bind_antidiagonal_insertionMultiset_singleton,
      Multiset.bind_assoc, ← Multiset.bind_add]
    refine Multiset.bind_congr fun p _ ↦ ?_
    rw [Multiset.add_bind, Multiset.bind_map, Multiset.bind_map]
  rw [hL]
  simp only [insertionMultiset_bind_singleton]
  rw [hR1, hR2]
  simp only [Multiset.map_add, Multiset.bind_add, Multiset.map_bind]
  abel

/-! ### The pre-Lie identity -/

/-- Grafting `S₁` then `S₂` into `T` is grafting `S₁ ◁ S₂` into `T` plus grafting both at once, the
degree-two case of the recursion by which [oudom-guin-2008] extend a pre-Lie product to the
symmetric algebra. -/
theorem insertSum_bind_insertSum (T S₁ S₂ : UnorderedTree α) :
    (T ◁ S₁).bind (· ◁ S₂) = (S₁ ◁ S₂).bind (T ◁ ·) + insertion T {S₁, S₂} := by
  rw [insertSum, insertion_bind_insertSum, insertionMultiset_singleton_singleton,
    Multiset.bind_map, add_comm, Multiset.pair_comm]
  rfl

/-- The associator of the grafting product is symmetric in its last two arguments, so that
`(T ◁ S₁) ◁ S₂ - T ◁ (S₁ ◁ S₂) = (T ◁ S₂) ◁ S₁ - T ◁ (S₂ ◁ S₁)`, here stated without
subtraction. -/
theorem insertSum_assoc_symm (T S₁ S₂ : UnorderedTree α) :
    (T ◁ S₁).bind (· ◁ S₂) + (S₂ ◁ S₁).bind (T ◁ ·) =
      (T ◁ S₂).bind (· ◁ S₁) + (S₁ ◁ S₂).bind (T ◁ ·) := by
  rw [insertSum_bind_insertSum, insertSum_bind_insertSum T S₂ S₁, Multiset.pair_comm]
  abel

end UnorderedTree
