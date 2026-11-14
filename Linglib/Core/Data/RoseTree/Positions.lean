module

public import Linglib.Core.Data.RoseTree.ReplaceAt
public import Mathlib.Data.List.Nodup
public import Mathlib.Order.Minimal

/-!
# Positions of a rose tree

`RoseTree.vertices` lists the addresses inside a tree in preorder, which is lexicographic order,
and `RoseTree.positionedLeaves` lists the leaf addresses in the order of the frontier, which is
precedence. The positions of a rose tree `t` form `RoseTree.Positions t`, a subtype of `TreePath`. Since
`validPaths t` is prefix-closed, the positions inherit the order structure of `TreePath`: the root
is the least position, the parent of a position and the meet of two positions are again positions,
and strict dominance is well founded, so `Positions t` is a rooted tree in the sense of
`Mathlib/Order/SuccPred/Tree.lean`. Covering in `Positions t` is covering in `TreePath`
(`Positions.covBy_iff`), so the daughters of a position are its valid daughters, and the subtree
at a position (`Positions.subtree`) has the subtrees at its covers as daughters
(`Positions.mem_children_subtree`) and the subtrees at the positions below it as subtrees
(`Positions.isSubtree_subtree`). A tree has finitely many positions, and the maximal ones are the
leaves (`Positions.isMax_iff`).

The positions whose subtree satisfies a predicate form `RoseTree.positionsWhere P t`, decidable
when the predicate is, which picks out the positions of a label, of a branching node, or of any
other condition on a node and what it dominates. Replacing the subtree at a position leaves the
positions outside it where they were, for a predicate that does not look below the root
(`mem_positionsWhere_replaceAt`). The topmost and bottommost of the positions are their `Minimal`
and `Maximal` members, the root being least, and both are decidable: the positions above one are
its prefixes, and those below it in the tree are among `vertices`.

## Main declarations

* `RoseTree.vertices`: the addresses in preorder.
* `RoseTree.Positions`: the positions of a tree, a rooted tree under the prefix order.
* `RoseTree.Positions.subtree`: the subtree at a position.
* `RoseTree.positionsWhere`: the positions whose subtree satisfies a predicate.
-/

@[expose] public section

namespace RoseTree

open Core.Order

variable {α : Type*}

/-! ### Enumerating the addresses -/

mutual
/-- `vertices t` lists the addresses of the vertices of `t` in preorder, the root `[]` first. -/
def vertices : RoseTree α → List (List ℕ)
  | node _ cs => [] :: verticesList cs
/-- `verticesList cs` lists the addresses of the vertices of the forest `cs`, each starting with
the index of its tree. -/
def verticesList : List (RoseTree α) → List (List ℕ)
  | [] => []
  | c :: cs => (vertices c).map (0 :: ·) ++ (verticesList cs).map (List.modifyHead (· + 1))
end

@[simp] theorem vertices_node (a : α) (cs : List (RoseTree α)) :
    vertices (node a cs) = [] :: verticesList cs := rfl

@[simp] theorem verticesList_nil : verticesList ([] : List (RoseTree α)) = [] := rfl

@[simp] theorem verticesList_cons (c : RoseTree α) (cs : List (RoseTree α)) :
    verticesList (c :: cs) =
      (vertices c).map (0 :: ·) ++ (verticesList cs).map (List.modifyHead (· + 1)) := rfl

theorem mem_verticesList {cs : List (RoseTree α)} {p : List ℕ} :
    p ∈ verticesList cs ↔ ∃ j q c, p = j :: q ∧ cs[j]? = some c ∧ q ∈ vertices c := by
  induction cs generalizing p with
  | nil => simp
  | cons c cs ih =>
    rw [verticesList_cons, List.mem_append, List.mem_map, List.mem_map]
    constructor
    · rintro (⟨q, hq, rfl⟩ | ⟨p', hp', rfl⟩)
      · exact ⟨0, q, c, rfl, rfl, hq⟩
      · obtain ⟨j, q, d, rfl, hd, hq⟩ := ih.mp hp'
        exact ⟨j + 1, q, d, rfl, hd, hq⟩
    · rintro ⟨_ | j, q, d, rfl, hd, hq⟩
      · exact .inl ⟨q, Option.some.inj hd ▸ hq, rfl⟩
      · exact .inr ⟨j :: q, ih.mpr ⟨j, q, d, rfl, hd, hq⟩, rfl⟩

theorem exists_cons_of_mem_verticesList {cs : List (RoseTree α)} {p : List ℕ}
    (hp : p ∈ verticesList cs) : ∃ j q, p = j :: q := by
  obtain ⟨j, q, -, rfl, -⟩ := mem_verticesList.mp hp
  exact ⟨j, q, rfl⟩

/-- The addresses listed by `vertices t` are exactly the addresses inside `t`. -/
theorem mem_vertices {t : RoseTree α} {p : List ℕ} :
    p ∈ t.vertices ↔ t[p]?.isSome := by
  induction t generalizing p with
  | node a cs ih =>
    rcases p with _ | ⟨j, q⟩
    · simp
    · simp only [vertices_node, List.mem_cons, reduceCtorEq, false_or, mem_verticesList,
        List.cons.injEq, getElem?_cons, children_node]
      constructor
      · rintro ⟨_, _, c, ⟨rfl, rfl⟩, hc, hq⟩
        rw [hc, Option.bind_some]
        exact (ih c (List.mem_of_getElem? hc)).mp hq
      · intro h
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp (Option.isSome_of_isSome_bind h)
        rw [hc, Option.bind_some] at h
        exact ⟨j, q, c, ⟨rfl, rfl⟩, hc, (ih c (List.mem_of_getElem? hc)).mpr h⟩

/-- The subtrees at the listed addresses are the listed subtrees. -/
theorem filterMap_getElem?_vertices (t : RoseTree α) :
    t.vertices.filterMap (t[·]?) = t.subtrees := by
  induction t with
  | node a cs ih =>
    rw [vertices_node, List.filterMap_cons_some (getElem?_nil _), subtrees_node]
    congr 1
    induction cs with
    | nil => rfl
    | cons c cs ihcs =>
      rw [verticesList_cons, List.filterMap_append, List.filterMap_map, List.filterMap_map,
        List.flatMap_cons, ← ih c List.mem_cons_self,
        ← ihcs fun d hd ↦ ih d (List.mem_cons_of_mem _ hd)]
      congr 1
      refine List.filterMap_congr fun p hp ↦ ?_
      obtain ⟨j, q, rfl⟩ := exists_cons_of_mem_verticesList hp
      rfl

mutual
theorem length_vertices : ∀ t : RoseTree α, t.vertices.length = t.numNodes
  | node _ cs => by rw [vertices_node, List.length_cons, length_verticesList cs, numNodes_node]
theorem length_verticesList : ∀ cs : List (RoseTree α),
    (verticesList cs).length = (cs.map numNodes).sum
  | [] => rfl
  | c :: cs => by
    rw [verticesList_cons, List.length_append, List.length_map, List.length_map,
      length_vertices c, length_verticesList cs, List.map_cons, List.sum_cons]
end

mutual
/-- The addresses in preorder increase lexicographically. -/
theorem pairwise_lt_vertices : ∀ t : RoseTree α, t.vertices.Pairwise (· < ·)
  | node _ cs => by
    rw [vertices_node, List.pairwise_cons]
    refine ⟨fun p hp ↦ ?_, pairwise_lt_verticesList cs⟩
    obtain ⟨j, q, rfl⟩ := exists_cons_of_mem_verticesList hp
    exact List.nil_lt_cons _ _
theorem pairwise_lt_verticesList : ∀ cs : List (RoseTree α), (verticesList cs).Pairwise (· < ·)
  | [] => List.Pairwise.nil
  | c :: cs => by
    rw [verticesList_cons, List.pairwise_append, List.pairwise_map, List.pairwise_map]
    refine ⟨(pairwise_lt_vertices c).imp fun h ↦ List.cons_lt_cons_iff.2 (.inr ⟨rfl, h⟩),
      (pairwise_lt_verticesList cs).imp_of_mem fun hp hq h ↦ ?_, ?_⟩
    · obtain ⟨_, _, rfl⟩ := exists_cons_of_mem_verticesList hp
      obtain ⟨_, _, rfl⟩ := exists_cons_of_mem_verticesList hq
      simpa [List.cons_lt_cons_iff] using h
    · simp only [List.mem_map]
      rintro _ ⟨p, -, rfl⟩ _ ⟨q, hq, rfl⟩
      obtain ⟨j, q, rfl⟩ := exists_cons_of_mem_verticesList hq
      exact List.cons_lt_cons_iff.2 (.inl (Nat.succ_pos j))
end

theorem nodup_vertices (t : RoseTree α) : t.vertices.Nodup :=
  (pairwise_lt_vertices t).nodup

/-- The subtrees of `t` with their positions, in preorder. -/
def positionedSubtrees (t : RoseTree α) : List (TreePath × RoseTree α) :=
  t.vertices.filterMap fun p ↦ t[p]?.map (⟨p⟩, ·)

theorem mem_positionedSubtrees {t s : RoseTree α} {p : TreePath} :
    (p, s) ∈ t.positionedSubtrees ↔ t[p]? = some s := by
  simp only [positionedSubtrees, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  refine ⟨fun ⟨_, _, _, hs, rfl, rfl⟩ ↦ hs, fun hs ↦ ?_⟩
  exact ⟨p.toList, mem_vertices.mpr (by rw [← getElem?_treePath, hs]; rfl), s, hs, rfl, rfl⟩

theorem pairwise_lt_positionedSubtrees (t : RoseTree α) :
    t.positionedSubtrees.Pairwise fun x y ↦ x.1.toList < y.1.toList :=
  (pairwise_lt_vertices t).filterMap _ fun p q h x hx y hy ↦ by
    simp only [Option.map_eq_some_iff] at hx hy
    obtain ⟨_, -, rfl⟩ := hx
    obtain ⟨_, -, rfl⟩ := hy
    exact h

theorem nodup_map_fst_positionedSubtrees (t : RoseTree α) :
    (t.positionedSubtrees.map Prod.fst).Nodup :=
  List.pairwise_map.mpr ((pairwise_lt_positionedSubtrees t).imp fun h he ↦ (he ▸ h).false)

/-- The address of the first subtree of `t`, in preorder, equal to `s`. -/
def addressOf? [DecidableEq α] (t s : RoseTree α) : Option (List ℕ) :=
  (t.positionedSubtrees.find? (·.2 = s)).map (·.1.toList)

theorem getElem?_of_addressOf? [DecidableEq α] {t s : RoseTree α} {p : List ℕ}
    (h : t.addressOf? s = some p) : t[p]? = some s := by
  obtain ⟨⟨q, s'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain rfl : s' = s := by simpa using List.find?_some hf
  exact mem_positionedSubtrees.mp (List.mem_of_find?_eq_some hf)

/-! ### The leaves with their addresses -/

/-- `positionedLeaves t` lists the leaves of `t` from left to right, each with its address. -/
def positionedLeaves : RoseTree α → List (TreePath × α) :=
  fold fun a ps ↦ match ps with
    | [] => [(⊥, a)]
    | ps => ps.zipIdx.flatMap fun (qs, i) ↦ qs.map fun x ↦ (⟨i :: x.1.toList⟩, x.2)

@[simp] theorem positionedLeaves_leaf (a : α) : positionedLeaves (node a []) = [(⊥, a)] := by
  simp only [positionedLeaves, fold_node, List.map_nil]

theorem positionedLeaves_node_of_ne_nil (a : α) {cs : List (RoseTree α)} (h : cs ≠ []) :
    positionedLeaves (node a cs) = cs.zipIdx.flatMap fun (c, i) ↦
      c.positionedLeaves.map fun x ↦ (⟨i :: x.1.toList⟩, x.2) := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil h
  rw [positionedLeaves, fold_node, List.map_cons]
  simp only [← List.map_cons, List.zipIdx_map, List.flatMap_map]
  rfl

/-- Forgetting the addresses leaves the frontier. -/
theorem map_snd_positionedLeaves (t : RoseTree α) :
    t.positionedLeaves.map Prod.snd = t.leafList := by
  induction t with
  | node a cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · simp
    rw [positionedLeaves_node_of_ne_nil a hcs, leafList_node_of_ne_nil a hcs, List.map_flatMap]
    conv_rhs => rw [← List.zipIdx_map_fst 0 cs, List.map_map, ← List.flatMap_def]
    refine List.flatMap_congr fun x hx ↦ ?_
    rw [List.map_map, Function.comp_apply, ← ih x.1 (List.fst_mem_of_mem_zipIdx hx)]
    rfl

/-- The listed addresses are exactly the addresses of the leaves. -/
theorem mem_positionedLeaves {t : RoseTree α} {p : TreePath} {a : α} :
    (p, a) ∈ t.positionedLeaves ↔ t[p]? = some (leaf a) := by
  obtain ⟨p⟩ := p
  induction t generalizing p with
  | node b cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · rcases p with _ | ⟨i, p⟩ <;> simp [TreePath.ext_iff, eq_comm]
    rcases p with _ | ⟨i, p⟩
    · simp [positionedLeaves_node_of_ne_nil b hcs, hcs]
    simp only [positionedLeaves_node_of_ne_nil b hcs, List.mem_flatMap, List.mem_map,
      getElem?_treePath, getElem?_cons, children_node, Option.bind_eq_some_iff, Prod.mk.injEq,
      TreePath.mk.injEq, List.cons.injEq]
    constructor
    · rintro ⟨⟨c, j⟩, hc, ⟨⟨q⟩, x⟩, hx, ⟨rfl, rfl⟩, rfl⟩
      have hc := List.mem_zipIdx_iff_getElem?.mp hc
      exact ⟨c, hc, (ih c (List.mem_of_getElem? hc) _).mp hx⟩
    · rintro ⟨c, hc, h⟩
      exact ⟨(c, i), List.mem_zipIdx_iff_getElem?.mpr hc, (⟨p⟩, a),
        (ih c (List.mem_of_getElem? hc) p).mpr h, ⟨rfl, rfl⟩, rfl⟩

/-- The leaf addresses, in the order of the frontier, ascend in precedence. -/
theorem pairwise_precedes_positionedLeaves (t : RoseTree α) :
    t.positionedLeaves.Pairwise fun x y ↦ x.1.Precedes y.1 := by
  induction t with
  | node a cs ih =>
    rcases eq_or_ne cs [] with rfl | hcs
    · simp
    have hlt : (cs.zipIdx 0).Pairwise fun x y ↦ x.2 < y.2 := by
      have := List.pairwise_lt_range' (s := 0) (n := cs.length)
      rwa [← List.zipIdx_map_snd, List.pairwise_map] at this
    rw [positionedLeaves_node_of_ne_nil a hcs, List.pairwise_flatMap]
    refine ⟨fun ⟨c, i⟩ hc ↦ ?_, hlt.imp fun hij x hx y hy ↦ ?_⟩
    · rw [List.pairwise_map]
      exact (ih c (List.fst_mem_of_mem_zipIdx hc)).imp fun h ↦ h.cons i
    · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hy
      exact TreePath.precedes_cons_of_lt hij _ _
/-! ### The positions as a rooted tree -/

/-- The valid positions of `t`, as a subtype of `TreePath`, form a rooted tree under the prefix
order. -/
abbrev Positions (t : RoseTree α) : Type := {p : TreePath // p ∈ t.validPaths}

/-- A tree has finitely many positions, those listed by `vertices`. -/
instance (t : RoseTree α) : Fintype t.Positions :=
  Fintype.subtype (t.vertices.map TreePath.mk).toFinset fun p ↦ by
    simp only [List.mem_toFinset, List.mem_map, mem_vertices]
    exact ⟨fun ⟨_, h, e⟩ ↦ e ▸ h, fun h ↦ ⟨_, h, rfl⟩⟩

namespace Positions

variable {t : RoseTree α}

/-- The root is the least position. -/
instance : OrderBot (Positions t) where
  bot := ⟨⊥, bot_mem_validPaths t⟩
  bot_le p := bot_le (a := p.val)

@[simp] theorem bot_val : ((⊥ : Positions t) : TreePath) = ⊥ := rfl

/-- The meet of two positions, their longest common prefix, is a position, since it dominates
either. -/
instance : SemilatticeInf (Positions t) :=
  Subtype.semilatticeInf fun _ _ hp _ ↦ validPaths_prefix_closed hp inf_le_left

@[simp] theorem inf_val (p q : Positions t) :
    ((p ⊓ q : Positions t) : TreePath) = p.val ⊓ q.val := rfl

/-- The parent of a position is a position. -/
instance : PredOrder (Positions t) where
  pred p := ⟨p.val.parent, validPaths_prefix_closed p.2 (TreePath.parent_le _)⟩
  pred_le p := TreePath.parent_le p.val
  min_of_le_pred {p} h := fun b hb ↦
    show p ≤ b from
      PredOrder.min_of_le_pred (α := TreePath)
        (show p.val ≤ Order.pred p.val from h)
        (show b.val ≤ p.val from hb)
  le_pred_of_lt {_ _} h :=
    TreePath.le_parent_of_lt (Subtype.coe_lt_coe.mpr h)

@[simp] theorem pred_val (p : Positions t) :
    ((Order.pred p : Positions t) : TreePath) = p.val.parent := rfl

theorem covBy_iff {p q : Positions t} : p ⋖ q ↔ p.val ⋖ q.val := by
  constructor
  · intro h
    have hpred : q.val.parent = p.val := congrArg Subtype.val (Order.pred_eq_of_covBy h)
    have hc : Order.pred q.val ⋖ q.val :=
      Order.pred_covBy_of_not_isMin (not_isMin_of_lt (Subtype.coe_lt_coe.mpr h.lt))
    rwa [TreePath.pred_eq_parent, hpred] at hc
  · intro h
    have hpred : Order.pred q = p := Subtype.ext (by rw [pred_val]; exact Order.pred_eq_of_covBy h)
    have hpq : p < q := Subtype.coe_lt_coe.mp h.lt
    have hc : Order.pred q ⋖ q := Order.pred_covBy_of_not_isMin (not_isMin_of_lt hpq)
    rwa [hpred] at hc

variable {p : Positions t} {c s : RoseTree α}

/-- The subtree of `t` at a position. -/
def subtree (p : Positions t) : RoseTree α := t[p.val]'p.2

theorem getElem?_eq (p : Positions t) : t[p.val.toList]? = some p.subtree :=
  (Option.some_get p.2).symm

/-- The subtrees at the positions are the subtrees, one per position. -/
theorem map_subtree_univ (t : RoseTree α) :
    (Finset.univ : Finset t.Positions).val.map subtree = (t.subtrees : Multiset (RoseTree α)) := by
  have hs : ∀ l : List (List ℕ), (∀ p ∈ l, t[p]?.isSome) →
      (l.filterMap (t[·]?)).map some = l.map (t[·]?) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨s, hp⟩ := Option.isSome_iff_exists.1 (hl p List.mem_cons_self)
      rw [List.filterMap_cons_some hp, List.map_cons, List.map_cons, hp,
        ih fun q hq ↦ hl q (List.mem_cons_of_mem _ hq)]
  have hv : (Finset.univ : Finset t.Positions).val.map Subtype.val =
      ↑(t.vertices.map TreePath.mk) := by
    refine (Multiset.Nodup.ext (Multiset.Nodup.map Subtype.val_injective Finset.univ.nodup)
      (Multiset.coe_nodup.2 ((nodup_vertices t).map fun _ _ h ↦ congrArg TreePath.toList h))).2
      fun x ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨q, -, rfl⟩ := Multiset.mem_map.1 hx
      exact Multiset.mem_coe.2 (List.mem_map.2 ⟨_, mem_vertices.2 q.2, rfl⟩)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hx)
      exact Multiset.mem_map.2 ⟨⟨_, mem_vertices.1 hp⟩, by simp, rfl⟩
  apply Multiset.map_injective (Option.some_injective _)
  rw [Multiset.map_map, show (some ∘ subtree : t.Positions → _) =
      ((t[·]?) ∘ TreePath.toList) ∘ Subtype.val from funext fun q ↦ (getElem?_eq q).symm,
    ← Multiset.map_map, hv, ← filterMap_getElem?_vertices, Multiset.map_coe, Multiset.map_coe,
    List.map_map, hs _ fun p hp ↦ mem_vertices.1 hp]
  rfl

@[simp] theorem subtree_bot : (⊥ : Positions t).subtree = t := rfl

theorem subtree_eq_iff : p.subtree = s ↔ t[p.val.toList]? = some s := by
  rw [getElem?_eq, Option.some_inj]

theorem isSubtree_subtree : IsSubtree s p.subtree ↔ ∃ q, p ≤ q ∧ q.subtree = s := by
  rw [isSubtree_iff_exists_getElem?]
  constructor
  · rintro ⟨r, hr⟩
    have hq : t[p.val.toList ++ r]? = some s := by
      rw [getElem?_append, getElem?_eq]; exact hr
    exact ⟨⟨⟨p.val.toList ++ r⟩, (getElem?_eq_some_iff.mp hq).1⟩,
      TreePath.le_def.2 (List.prefix_append _ _), subtree_eq_iff.2 hq⟩
  · rintro ⟨q, hpq, rfl⟩
    obtain ⟨r, hr⟩ := TreePath.le_def.1 hpq
    refine ⟨r, ?_⟩
    have := q.getElem?_eq
    rwa [← hr, getElem?_append, getElem?_eq, Option.bind_some] at this

theorem mem_children_subtree : c ∈ p.subtree.children ↔ ∃ q, p ⋖ q ∧ q.subtree = c := by
  simp only [covBy_iff, TreePath.covBy_iff]
  constructor
  · intro hc
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
    have hq : t[p.val.toList ++ [i]]? = some c := by
      simp [getElem?_append, getElem?_eq, hi]
    exact ⟨⟨⟨p.val.toList ++ [i]⟩, (getElem?_eq_some_iff.mp hq).1⟩, ⟨i, rfl⟩,
      subtree_eq_iff.2 hq⟩
  · rintro ⟨q, ⟨i, hi⟩, rfl⟩
    have := q.getElem?_eq
    rw [hi, getElem?_append, getElem?_eq, Option.bind_some] at this
    exact List.mem_of_getElem? (by simpa using this)

theorem isMax_iff : IsMax p ↔ p.subtree.children = [] := by
  refine ⟨fun h ↦ List.eq_nil_iff_forall_not_mem.2 fun c hc ↦ ?_, fun h q hpq ↦ ?_⟩
  · obtain ⟨q, hq, -⟩ := mem_children_subtree.1 hc
    exact hq.lt.not_ge (h hq.le)
  · obtain ⟨s, hs⟩ := TreePath.le_def.1 hpq
    rcases s with _ | ⟨i, s⟩
    · exact (Subtype.ext (TreePath.ext (by simpa using hs.symm)) : q = p).le
    · obtain ⟨u, hu, hi⟩ := mem_validPaths_append_singleton_iff.1
        (validPaths_prefix_closed q.2 (TreePath.le_def.2 ⟨s, by simp [← hs]⟩) :
          (⟨p.val.toList ++ [i]⟩ : TreePath) ∈ t.validPaths)
      obtain rfl := Option.some.inj (p.getElem?_eq.symm.trans hu)
      simp [h] at hi

end Positions

/-! ### Positions satisfying a predicate -/

section PositionsWhere

variable {P Q : RoseTree α → Prop} {t : RoseTree α} {p : TreePath}

/-- The positions of `t` whose subtree satisfies `P`. -/
def positionsWhere (P : RoseTree α → Prop) (t : RoseTree α) : Set TreePath :=
  {p | ∃ s ∈ t[p.toList]?, P s}

theorem mem_positionsWhere : p ∈ positionsWhere P t ↔ ∃ s ∈ t[p.toList]?, P s := Iff.rfl

instance [DecidablePred P] (t : RoseTree α) : DecidablePred (· ∈ positionsWhere P t) := fun _ ↦
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem positionsWhere_subset_validPaths (P : RoseTree α → Prop) (t : RoseTree α) :
    positionsWhere P t ⊆ t.validPaths := by
  rintro p ⟨s, hs, -⟩
  exact (getElem?_eq_some_iff.mp hs).1

theorem positionsWhere_mono (h : ∀ s, P s → Q s) (t : RoseTree α) :
    positionsWhere P t ⊆ positionsWhere Q t :=
  fun _ ⟨s, hs, hP⟩ ↦ ⟨s, hs, h s hP⟩

theorem positionsWhere_or (P Q : RoseTree α → Prop) (t : RoseTree α) :
    positionsWhere (fun s ↦ P s ∨ Q s) t = positionsWhere P t ∪ positionsWhere Q t := by
  ext p
  simp only [positionsWhere, Set.mem_ofPred_eq, Set.mem_union, and_or_left, exists_or]

theorem positionsWhere_and (P Q : RoseTree α → Prop) (t : RoseTree α) :
    positionsWhere (fun s ↦ P s ∧ Q s) t = positionsWhere P t ∩ positionsWhere Q t := by
  ext p
  simp only [positionsWhere, Set.mem_ofPred_eq, Set.mem_inter_iff, Option.mem_def]
  grind

theorem positionsWhere_map {β : Type*} (f : α → β) (P : RoseTree β → Prop) (t : RoseTree α) :
    positionsWhere P (t.map f) = positionsWhere (fun s ↦ P (s.map f)) t := by
  ext p
  simp [positionsWhere, getElem?_map, Option.mem_def]

theorem mem_positionsWhere_replaceAt
    (hP : ∀ s i q (new : RoseTree α), P (s.replaceAt (i :: q) new) ↔ P s) {c : TreePath}
    (h : ¬ c ≤ p) (new : RoseTree α) :
    p ∈ positionsWhere P (t.replaceAt c.toList new) ↔ p ∈ positionsWhere P t := by
  by_cases hpc : p ≤ c
  · obtain ⟨_ | ⟨i, q⟩, hq⟩ := hpc
    · exact absurd (TreePath.le_def.mpr (by simp [← hq])) h
    rw [mem_positionsWhere, mem_positionsWhere, getElem?_replaceAt_of_prefix ⟨_, hq⟩, ← hq,
      List.drop_left]
    simp [hP]
  · rw [mem_positionsWhere, mem_positionsWhere, getElem?_replaceAt_of_not_prefix h hpc]

theorem minimal_mem_positionsWhere_iff :
    Minimal (· ∈ positionsWhere P t) p ↔
      p ∈ positionsWhere P t ∧ ∀ q ∈ p.toList.inits, ⟨q⟩ ≠ p → ⟨q⟩ ∉ positionsWhere P t := by
  rw [minimal_iff_forall_lt]
  refine and_congr_right fun _ ↦ ⟨fun h q hq hne ↦ h ?_, fun h q hq ↦ ?_⟩
  · exact lt_of_le_of_ne (TreePath.le_def.mpr ((List.mem_inits _ _).mp hq)) hne
  · exact h q.toList ((List.mem_inits _ _).mpr (TreePath.le_def.mp hq.le)) hq.ne

instance [DecidablePred P] : Decidable (Minimal (· ∈ positionsWhere P t) p) :=
  decidable_of_iff _ minimal_mem_positionsWhere_iff.symm

theorem maximal_mem_positionsWhere_iff :
    Maximal (· ∈ positionsWhere P t) p ↔
      p ∈ positionsWhere P t ∧ ∀ q ∈ t.vertices, p < ⟨q⟩ → ⟨q⟩ ∉ positionsWhere P t := by
  rw [maximal_iff_forall_gt]
  refine and_congr_right fun _ ↦ ⟨fun h q _ hpq ↦ h hpq, fun h q hpq hq ↦ ?_⟩
  refine h q.toList (mem_vertices.mpr ?_) hpq hq
  obtain ⟨s, hs, -⟩ := hq
  rw [Option.mem_def.mp hs]
  rfl

instance [DecidablePred P] : Decidable (Maximal (· ∈ positionsWhere P t) p) :=
  decidable_of_iff _ maximal_mem_positionsWhere_iff.symm

end PositionsWhere

end RoseTree
