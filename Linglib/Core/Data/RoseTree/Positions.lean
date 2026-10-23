module

public import Linglib.Core.Data.RoseTree.Get
public import Mathlib.Order.Minimal

/-!
# Positions of a rose tree

The positions of a rose tree `t` form `RoseTree.Positions t`, a subtype of `TreePath`. Since
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

* `RoseTree.Positions`: the positions of a tree, a rooted tree under the prefix order.
* `RoseTree.Positions.subtree`: the subtree at a position.
* `RoseTree.positionsWhere`: the positions whose subtree satisfies a predicate.
-/

@[expose] public section

namespace RoseTree

open Core.Order

variable {α : Type*}

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
def subtree (p : Positions t) : RoseTree α := (t.subtreeAt p.val.toList).get p.2

theorem subtreeAt_eq (p : Positions t) : t.subtreeAt p.val.toList = some p.subtree :=
  (Option.some_get p.2).symm

/-- The subtrees at the positions are the subtrees, one per position. -/
theorem map_subtree_univ (t : RoseTree α) :
    (Finset.univ : Finset t.Positions).val.map subtree = (t.subtrees : Multiset (RoseTree α)) := by
  have hs : ∀ l : List (List ℕ), (∀ p ∈ l, (t.subtreeAt p).isSome) →
      (l.filterMap t.subtreeAt).map some = l.map t.subtreeAt := by
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
      (t.subtreeAt ∘ TreePath.toList) ∘ Subtype.val from funext fun q ↦ (subtreeAt_eq q).symm,
    ← Multiset.map_map, hv, ← filterMap_subtreeAt_vertices, Multiset.map_coe, Multiset.map_coe,
    List.map_map, hs _ fun p hp ↦ mem_vertices.1 hp]
  rfl

@[simp] theorem subtree_bot : (⊥ : Positions t).subtree = t := rfl

theorem subtree_eq_iff : p.subtree = s ↔ t.subtreeAt p.val.toList = some s := by
  rw [subtreeAt_eq, Option.some_inj]

theorem isSubtree_subtree : IsSubtree s p.subtree ↔ ∃ q, p ≤ q ∧ q.subtree = s := by
  rw [isSubtree_iff_exists_subtreeAt]
  constructor
  · rintro ⟨r, hr⟩
    have hq : t.subtreeAt (p.val.toList ++ r) = some s := by
      rw [subtreeAt_append, subtreeAt_eq]; exact hr
    exact ⟨⟨⟨p.val.toList ++ r⟩, by simp [validPaths, hq]⟩,
      TreePath.le_def.2 (List.prefix_append _ _), subtree_eq_iff.2 hq⟩
  · rintro ⟨q, hpq, rfl⟩
    obtain ⟨r, hr⟩ := TreePath.le_def.1 hpq
    refine ⟨r, ?_⟩
    have := q.subtreeAt_eq
    rwa [← hr, subtreeAt_append, subtreeAt_eq, Option.bind_some] at this

theorem mem_children_subtree : c ∈ p.subtree.children ↔ ∃ q, p ⋖ q ∧ q.subtree = c := by
  simp only [covBy_iff, TreePath.covBy_iff]
  constructor
  · intro hc
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hc
    have hq : t.subtreeAt (p.val.toList ++ [i]) = some c := by
      simp [subtreeAt_append, subtreeAt_eq, hi]
    exact ⟨⟨⟨p.val.toList ++ [i]⟩, by simp [validPaths, hq]⟩, ⟨i, rfl⟩, subtree_eq_iff.2 hq⟩
  · rintro ⟨q, ⟨i, hi⟩, rfl⟩
    have := q.subtreeAt_eq
    rw [hi, subtreeAt_append, subtreeAt_eq, Option.bind_some] at this
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
      obtain rfl := Option.some.inj (p.subtreeAt_eq.symm.trans hu)
      simp [h] at hi

end Positions

/-! ### Positions satisfying a predicate -/

section PositionsWhere

variable {P Q : RoseTree α → Prop} {t : RoseTree α} {p : TreePath}

/-- The positions of `t` whose subtree satisfies `P`. -/
def positionsWhere (P : RoseTree α → Prop) (t : RoseTree α) : Set TreePath :=
  {p | ∃ s ∈ t.subtreeAt p.toList, P s}

theorem mem_positionsWhere : p ∈ positionsWhere P t ↔ ∃ s ∈ t.subtreeAt p.toList, P s := Iff.rfl

instance [DecidablePred P] (t : RoseTree α) : DecidablePred (· ∈ positionsWhere P t) := fun _ ↦
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

theorem positionsWhere_subset_validPaths (P : RoseTree α → Prop) (t : RoseTree α) :
    positionsWhere P t ⊆ t.validPaths := by
  rintro p ⟨s, hs, -⟩
  simp_all [validPaths, Option.mem_def]

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
  simp [positionsWhere, subtreeAt_map, Option.mem_def]

theorem mem_positionsWhere_replaceAt
    (hP : ∀ s i q (new : RoseTree α), P (s.replaceAt (i :: q) new) ↔ P s) {c : TreePath}
    (h : ¬ c ≤ p) (new : RoseTree α) :
    p ∈ positionsWhere P (t.replaceAt c.toList new) ↔ p ∈ positionsWhere P t := by
  by_cases hpc : p ≤ c
  · obtain ⟨_ | ⟨i, q⟩, hq⟩ := hpc
    · exact absurd (TreePath.le_def.mpr (by simp [← hq])) h
    rw [mem_positionsWhere, mem_positionsWhere, subtreeAt_replaceAt_of_prefix ⟨_, hq⟩, ← hq,
      List.drop_left]
    simp [hP]
  · rw [mem_positionsWhere, mem_positionsWhere, subtreeAt_replaceAt_of_not_prefix h hpc]

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
