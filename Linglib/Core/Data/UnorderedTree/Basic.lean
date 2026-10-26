/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.Basic
public import Linglib.Core.Data.RoseTree.Perm
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Forall2
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.MapFold

/-!
# Unordered rooted trees

An unordered rooted tree with vertices labelled in `α` is a `RoseTree α` modulo the permutation
of children at every vertex: the quotient `UnorderedTree α := Quotient RoseTree.isSetoid`. In the
Connes–Kreimer literature, as in Foissy's introduction, these are the rooted trees and the
ordered ones the planar rooted trees. The identity criterion is `RoseTree.Perm`
(`Core/Data/RoseTree/Perm.lean`); this file owns the quotient: the projection `mk`, the lifting
API, the lifted invariants, and the constructor `node` on `Multiset` children, under which the
grafting `B⁺` of a multiset of trees is well defined.

## Main definitions

* `UnorderedTree`, `UnorderedTree.mk`: the quotient and its projection; operations descend
  through `Quotient.lift` and proofs through `Quotient.inductionOn`, as for `Multiset`.
* `UnorderedTree.cons`: adjoin a tree as a further child of the root, the transport of the list
  cons on children; it is left-commutative, so `Multiset.foldr` builds the constructor
  `UnorderedTree.node` on a multiset of children computably.
* `UnorderedTree.induction_on`, `UnorderedTree.fold`: induction and recursion on a tree as a
  label over a multiset of trees.
* `UnorderedTree.para`: recursion in which each step also sees the children themselves, so that
  subtree-sensitive functions are defined on the quotient with no invariance proof.

## References

* [L. Foissy, *An introduction to Hopf algebras of trees*][foissy-introduction-hopf-algebras-trees]
-/

@[expose] public section

open RoseTree

/-! ### The quotient type -/

/-- An unordered rooted tree with `α`-labelled vertices, the quotient of `RoseTree α` by the
permutation of children at every vertex (`RoseTree.Perm`). -/
def UnorderedTree (α : Type*) : Type _ := Quotient (RoseTree.isSetoid : Setoid (RoseTree α))

namespace UnorderedTree

variable {α β γ : Type*}

/-- The canonical projection from ordered to nonplanar trees. -/
def mk (t : RoseTree α) : UnorderedTree α := Quotient.mk _ t

theorem mk_eq_mk_iff {t s : RoseTree α} : mk t = mk s ↔ RoseTree.Perm t s :=
  Quotient.eq

@[simp] theorem quot_mk_eq_mk (t : RoseTree α) : (⟦t⟧ : UnorderedTree α) = mk t := rfl

/-! ### Leaves and lifted counts -/

/-- A nonplanar leaf labeled `a`. -/
abbrev leaf (a : α) : UnorderedTree α := mk (RoseTree.leaf a)

/-- The number of vertices of a nonplanar tree. -/
def numNodes : UnorderedTree α → Nat :=
  Quotient.lift RoseTree.numNodes (fun _ _ ↦ RoseTree.numNodes_perm)

@[simp] theorem numNodes_mk (t : RoseTree α) : (mk t).numNodes = t.numNodes := rfl

@[simp] theorem numNodes_leaf (a : α) : (leaf a : UnorderedTree α).numNodes = 1 := by simp

/-- The number of childless vertices of a nonplanar tree. -/
def numLeaves : UnorderedTree α → Nat :=
  Quotient.lift RoseTree.numLeaves (fun _ _ ↦ RoseTree.numLeaves_perm)

@[simp] theorem numLeaves_mk (t : RoseTree α) : (mk t).numLeaves = t.numLeaves := rfl

@[simp] theorem numLeaves_leaf (a : α) : (leaf a : UnorderedTree α).numLeaves = 1 := by
  simp

/-- The number of children of the root. -/
def arity : UnorderedTree α → Nat :=
  Quotient.lift RoseTree.arity (fun _ _ ↦ RoseTree.arity_perm)

@[simp] theorem arity_mk (t : RoseTree α) : (mk t).arity = t.arity := rfl

@[simp] theorem arity_leaf (a : α) : (leaf a : UnorderedTree α).arity = 0 := rfl

/-- The number of vertices on a longest root-to-leaf path. -/
def height : UnorderedTree α → Nat :=
  Quotient.lift RoseTree.height (fun _ _ ↦ RoseTree.height_perm)

@[simp] theorem height_mk (t : RoseTree α) : (mk t).height = t.height := rfl

@[simp] theorem height_leaf (a : α) : (leaf a : UnorderedTree α).height = 1 := by simp

/-! ### Destructors and node injectivity

The root value and the children (as a multiset of nonplanar trees) are
`RoseTree.Perm`-invariant, so they descend to `UnorderedTree`. Node injectivity,
`mk_node_eq_mk_node_iff`, is `RoseTree.perm_node_iff` read through `mk`. -/

/-- The root value of a nonplanar tree. -/
def value : UnorderedTree α → α :=
  Quotient.lift RoseTree.value (fun _ _ h ↦ h.value_eq)

@[simp] theorem value_mk (t : RoseTree α) : (mk t).value = t.value := rfl

theorem perm_children_map_mk {t s : RoseTree α} (h : RoseTree.Perm t s) :
    (↑(t.children.map mk) : Multiset (UnorderedTree α)) = ↑(s.children.map mk) := by
  rw [← Multiset.map_coe, ← Multiset.map_coe, ← Multiset.rel_eq, Multiset.rel_map]
  exact h.children_rel.mono fun _ _ _ _ ↦ mk_eq_mk_iff.mpr

/-- The children of a nonplanar tree, as a multiset of nonplanar trees. -/
def children : UnorderedTree α → Multiset (UnorderedTree α) :=
  Quotient.lift (fun t ↦ ↑(t.children.map mk)) (fun _ _ ↦ perm_children_map_mk)

@[simp] theorem children_mk (t : RoseTree α) :
    (mk t).children = ↑(t.children.map mk) := rfl

theorem mk_node_eq_mk_node_iff {a b : α} {cs ds : List (RoseTree α)} :
    mk (.node a cs) = mk (.node b ds) ↔
      a = b ∧ (↑(cs.map mk) : Multiset (UnorderedTree α)) = ↑(ds.map mk) := by
  rw [mk_eq_mk_iff, perm_node_iff, ← Multiset.map_coe, ← Multiset.map_coe, ← Multiset.rel_eq,
    Multiset.rel_map]
  simp only [mk_eq_mk_iff]

/-! ### Adjoining a child, and the node constructor

`cons c t` adjoins `c` as a further child of the root of `t`; it is the transport of the list
cons on children lists and is left-commutative, so `node a F` is its `Multiset.foldr` over the
children `F` starting from the leaf `a`. Both are computable, and `node_mk_tree_list` reads
`node` back on a list of planar children. -/

/-- Adjoin a tree as a further child of the root. -/
def cons (c t : UnorderedTree α) : UnorderedTree α :=
  Quotient.liftOn₂ c t (fun c t ↦ mk (.node t.value (c :: t.children))) fun _ _ _ _ hc ht ↦
    mk_eq_mk_iff.mpr (perm_node_iff.mpr ⟨ht.value_eq, by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe]
      exact ht.children_rel.cons hc⟩)

@[simp] theorem cons_mk (c : RoseTree α) (a : α) (cs : List (RoseTree α)) :
    cons (mk c) (mk (.node a cs)) = mk (.node a (c :: cs)) := rfl

instance : LeftCommutative (cons (α := α)) :=
  ⟨fun c d t ↦ Quotient.inductionOn₃ c d t fun _ _ t ↦ by
    obtain ⟨a, cs⟩ := t
    exact mk_eq_mk_iff.mpr (.node (.swap ..))⟩

/-- Build an unordered tree from a label and a multiset of children, by adjoining the children
one at a time to the leaf. -/
def node (a : α) (F : Multiset (UnorderedTree α)) : UnorderedTree α := F.foldr cons (leaf a)

@[simp] theorem node_zero (a : α) : node a (0 : Multiset (UnorderedTree α)) = leaf a := rfl

theorem node_cons (a : α) (c : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    node a (c ::ₘ F) = cons c (node a F) :=
  Multiset.foldr_cons ..

@[simp] theorem cons_node (a : α) (c : UnorderedTree α) (F : Multiset (UnorderedTree α)) :
    cons c (node a F) = node a (c ::ₘ F) :=
  (node_cons a c F).symm

theorem node_mk_tree_list (a : α) (ps : List (RoseTree α)) :
    node a (Multiset.ofList (ps.map mk)) = mk (.node a ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rw [List.map_cons, ← Multiset.cons_coe, node_cons, ih]; rfl

theorem node_pair_mk (a : α) (p q : RoseTree α) :
    node a {mk p, mk q} = mk (.node a [p, q]) :=
  node_mk_tree_list a [p, q]

@[elab_as_elim]
theorem forest_inductionOn {motive : Multiset (UnorderedTree α) → Prop}
    (F : Multiset (UnorderedTree α))
    (h : ∀ cs : List (RoseTree α), motive (Multiset.ofList (cs.map mk))) : motive F := by
  obtain ⟨cs, rfl⟩ : ∃ cs : List (RoseTree α), F = ↑(cs.map mk) := by
    induction F using Multiset.induction_on with
    | empty => exact ⟨[], rfl⟩
    | cons x F ih =>
      obtain ⟨cs, rfl⟩ := ih
      obtain ⟨c, rfl⟩ := Quotient.exists_rep x
      exact ⟨c :: cs, rfl⟩
  exact h cs

/-! ### Structural induction and recursion

An unordered tree is a label over a multiset of unordered trees. `induction_on`, `fold` and
`para` are the induction, recursion and paramorphism principles of that description; a function
defined through them needs no proof of invariance under `RoseTree.Perm`. -/

/-- Induction on an unordered tree proves `motive t` for all `t` from `motive (node a F)` given
`motive c` for every child `c ∈ F`. -/
@[elab_as_elim, induction_eliminator]
theorem induction_on {motive : UnorderedTree α → Prop} (t : UnorderedTree α)
    (node : ∀ (a : α) (F : Multiset (UnorderedTree α)), (∀ c ∈ F, motive c) → motive (node a F)) :
    motive t := by
  induction t using Quotient.inductionOn with
  | h t =>
    induction t with
    | node a cs ih =>
      rw [quot_mk_eq_mk, ← node_mk_tree_list]
      refine node a _ fun c hc ↦ ?_
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hc)
      exact ih c' hc'

/-- The catamorphism replaces each `node a F` by `f a` of the multiset of folded children. -/
def fold (f : α → Multiset β → β) : UnorderedTree α → β :=
  Quotient.lift (RoseTree.fold fun a bs ↦ f a bs) fun _ _ ↦
    RoseTree.fold_perm fun a _ _ h ↦ congrArg (f a) (Multiset.coe_eq_coe.2 h)

theorem fold_mk (f : α → Multiset β → β) (t : RoseTree α) :
    fold f (mk t) = t.fold fun a bs ↦ f a bs := rfl

@[simp] theorem fold_node (f : α → Multiset β → β) (a : α) (F : Multiset (UnorderedTree α)) :
    fold f (node a F) = f a (F.map (fold f)) := by
  induction F using forest_inductionOn with
  | h cs => rw [node_mk_tree_list, fold_mk, RoseTree.fold_node, Multiset.map_coe, List.map_map]; rfl

/-- The paramorphism passes `f a` each child together with its value. It is the `fold` into
pairs whose first component rebuilds the subtree. -/
def para (f : α → Multiset (UnorderedTree α × β) → β) (t : UnorderedTree α) : β :=
  (t.fold fun a ps ↦ (node a (ps.map Prod.fst), f a ps)).2

private theorem fst_fold_para (f : α → Multiset (UnorderedTree α × β) → β) (t : UnorderedTree α) :
    (t.fold fun a ps ↦ (node a (ps.map Prod.fst), f a ps)).1 = t := by
  induction t with
  | node a F ih =>
    rw [fold_node, Multiset.map_map]
    exact congrArg (node a) ((Multiset.map_congr rfl ih).trans F.map_id')

@[simp] theorem para_node (f : α → Multiset (UnorderedTree α × β) → β) (a : α)
    (F : Multiset (UnorderedTree α)) :
    para f (node a F) = f a (F.map fun t ↦ (t, para f t)) := by
  rw [para, fold_node]
  exact congrArg (f a) (Multiset.map_congr rfl fun t _ ↦ Prod.ext (fst_fold_para f t) rfl)

/-! ### The destructors of a `node` -/

@[simp] theorem value_node (a : α) (F : Multiset (UnorderedTree α)) : value (node a F) = a := by
  induction F using forest_inductionOn with
  | h ps => rw [node_mk_tree_list]; rfl

@[simp] theorem children_node (a : α) (F : Multiset (UnorderedTree α)) :
    children (node a F) = F := by
  induction F using forest_inductionOn with
  | h ps => rw [node_mk_tree_list]; rfl

theorem node_eta (t : UnorderedTree α) : node (value t) (children t) = t := by
  induction t with
  | node a F => rw [value_node, children_node]

@[simp] theorem node_inj {a b : α} {F G : Multiset (UnorderedTree α)} :
    node a F = node b G ↔ a = b ∧ F = G :=
  ⟨fun h ↦ ⟨by simpa using congrArg value h, by simpa using congrArg children h⟩,
    fun ⟨ha, hF⟩ ↦ ha ▸ hF ▸ rfl⟩

theorem node_injective (a : α) : Function.Injective (node a) := fun _ _ h ↦ (node_inj.mp h).2

/-! ### Node count of a `node` -/

theorem numNodes_pos (t : UnorderedTree α) : 0 < t.numNodes :=
  Quotient.inductionOn t RoseTree.numNodes_pos

@[simp] theorem numNodes_node (a : α) (F : Multiset (UnorderedTree α)) :
    (node a F).numNodes = (F.map numNodes).sum + 1 := by
  induction F using forest_inductionOn with
  | h ps =>
    rw [node_mk_tree_list, numNodes_mk, RoseTree.numNodes_node, Multiset.map_coe,
      Multiset.sum_coe, List.map_map]
    rfl

/-! ### Height of a `node` -/

theorem height_lt_of_mem (T : UnorderedTree α) (F : Multiset (UnorderedTree α))
    (hT : T ∈ F) (a : α) : T.height < (node a F).height := by
  induction F using forest_inductionOn with
  | h ps =>
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hT)
    rw [node_mk_tree_list]
    exact RoseTree.height_lt_of_mem (t := RoseTree.node a ps) hc

/-! ### Functoriality -/

/-- Relabel every vertex of a nonplanar tree. -/
def map (f : α → β) : UnorderedTree α → UnorderedTree β :=
  Quotient.map (RoseTree.map f)
    (fun _ _ ↦ RoseTree.Perm.map f)

theorem map_mk (f : α → β) (t : RoseTree α) :
    map f (mk t) = mk (RoseTree.map f t) := rfl

theorem map_leaf (f : α → β) (a : α) :
    map f (leaf a) = leaf (f a) := by
  show map f (mk (RoseTree.leaf a)) = mk (RoseTree.leaf (f a))
  rw [map_mk, RoseTree.map_leaf]

@[simp] theorem map_id (t : UnorderedTree α) : map id t = t :=
  Quotient.inductionOn t fun p ↦ congrArg mk p.id_map

theorem map_map (f : α → β) (g : β → γ) (t : UnorderedTree α) :
    map g (map f t) = map (g ∘ f) t :=
  Quotient.inductionOn t fun p ↦ congrArg mk (p.comp_map f g).symm

theorem map_node (f : α → β) (a : α) (cs : Multiset (UnorderedTree α)) :
    map f (node a cs) = node (f a) (cs.map (map f)) := by
  refine forest_inductionOn cs fun ps ↦ ?_
  rw [node_mk_tree_list, map_mk, RoseTree.map_node,
    show (Multiset.ofList (ps.map mk)).map (map f)
        = Multiset.ofList ((ps.map (RoseTree.map f)).map mk) by
      simp [List.map_map, Function.comp_def, map_mk],
    node_mk_tree_list]

@[simp] theorem value_map (f : α → β) (t : UnorderedTree α) : (map f t).value = f t.value :=
  Quotient.inductionOn t fun p ↦ RoseTree.value_map f p

theorem map_injective {f : α → β} (hf : Function.Injective f) : Function.Injective (map f) := by
  cases isEmpty_or_nonempty α with
  | inl h => exact fun t _ _ ↦ (h.false t.value).elim
  | inr _ =>
    obtain ⟨g, hg⟩ := hf.hasLeftInverse
    exact Function.LeftInverse.injective (g := map g) fun t ↦ by
      rw [map_map, hg.comp_eq_id, map_id]

/-! ### Counting interactions -/

@[simp] theorem numNodes_map (f : α → β) (t : UnorderedTree α) :
    (map f t).numNodes = t.numNodes :=
  Quotient.inductionOn t (RoseTree.numNodes_map f)

@[simp] theorem height_map (f : α → β) (t : UnorderedTree α) : (map f t).height = t.height :=
  Quotient.inductionOn t (RoseTree.height_map f)

@[simp] theorem arity_map (f : α → β) (t : UnorderedTree α) : (map f t).arity = t.arity :=
  Quotient.inductionOn t (RoseTree.arity_map f)

@[simp] theorem numLeaves_map (f : α → β) (t : UnorderedTree α) :
    (map f t).numLeaves = t.numLeaves :=
  Quotient.inductionOn t (RoseTree.numLeaves_map f)

end UnorderedTree
