/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Data.RoseTree.ReplaceAt
public import Mathlib.Order.Hom.Basic

/-!
# One-hole contexts of a rose tree

A frame is a node with one child missing, and a context is a list of frames, the outermost
first: a tree with a hole in it. Plugging a tree into a context fills the hole, and the positions
of the plugged tree are carried into the result by an order embedding, so that the subtree at a
carried position is the subtree it was.

## Main definitions

* `RoseTree.Frame`, `RoseTree.Context`: a node with one child missing, and a list of them.
* `RoseTree.Context.plug`: the tree that a context makes of a tree.
* `RoseTree.Context.embed`: the order embedding of the positions of a tree into those of the tree
  a context makes of it.

## Main results

* `RoseTree.Context.getElem?_plug_embed`: plugging leaves the subtrees of the plugged tree where
  the embedding carries their positions.
* `RoseTree.Context.replaceAt_plug`: replacing what fills the hole is plugging the replacement.
* `RoseTree.Context.le_embed_iff`: a position above an embedded one is above the hole or is
  itself embedded.

## Implementation notes

A context is a list, so that contexts compose by `++` and `plug_append`, `path_append` and
`embed_append` say that they act on trees, addresses and positions.
-/

@[expose] public section

/-- Modifying a list at the length of a prefix modifies the element after the prefix. -/
theorem List.modify_append_cons_length {α : Type*} (l r : List α) (a : α) (f : α → α) :
    (l ++ a :: r).modify l.length f = l ++ f a :: r := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

namespace RoseTree


variable {α : Type*}

/-- A node with one child missing, between the children `before` it and those `after` it. -/
structure Frame (α : Type*) where
  /-- The label of the node. -/
  value : α
  /-- The children to the left of the hole. -/
  before : List (RoseTree α) := []
  /-- The children to the right of the hole. -/
  after : List (RoseTree α) := []

/-- The node that a frame makes of a tree put in its hole. -/
def Frame.plug (f : Frame α) (t : RoseTree α) : RoseTree α :=
  node f.value (f.before ++ t :: f.after)

/-- A tree with a hole in it, as the frames from its root down to the hole. -/
abbrev Context (α : Type*) := List (Frame α)

namespace Context

variable (c d : Context α) (f : Frame α) (s t : RoseTree α)

/-- The tree that a context makes of a tree put in its hole. -/
def plug : RoseTree α := c.foldr Frame.plug t

/-- The address of the hole. -/
def path : List ℕ := c.map (·.before.length)

@[simp] theorem plug_nil : plug [] t = t := rfl

@[simp] theorem plug_cons : plug (f :: c) t = f.plug (plug c t) := rfl

@[simp] theorem path_nil : path ([] : Context α) = [] := rfl

@[simp] theorem path_cons : path (f :: c) = f.before.length :: path c := rfl

@[simp] theorem plug_append : plug (c ++ d) t = plug c (plug d t) := List.foldr_append

@[simp] theorem path_append : path (c ++ d) = path c ++ path d := List.map_append

/-- An address above the hole splits the context there. -/
theorem exists_append_of_prefix_path {c : Context α} {r : List ℕ} (h : r <+: path c) :
    ∃ c₁ c₂, c₁ ++ c₂ = c ∧ path c₁ = r :=
  ⟨c.take r.length, c.drop r.length, List.take_append_drop _ _, by
    rw [path, List.map_take]; exact (List.prefix_iff_eq_take.mp h).symm⟩

@[simp] theorem getElem?_plug_append (q : List ℕ) : (plug c t)[path c ++ q]? = t[q]? := by
  induction c with
  | nil => rfl
  | cons f c ih => simp [Frame.plug, ih]

@[simp] theorem getElem?_plug_path : (plug c t)[path c]? = some t := by
  simpa using getElem?_plug_append c t []

/-- Replacing what fills the hole of a context is plugging the replacement. -/
@[simp] theorem replaceAt_plug : (plug c s).replaceAt (path c) t = plug c t := by
  induction c with
  | nil => simp
  | cons f c ih => simp [Frame.plug, replaceAt_cons, List.modify_append_cons_length, ih]

/-- The position that a position of a tree has in the tree a context makes of it. -/
def embed : GornAddress ↪o GornAddress := GornAddress.mulLeft ⟨path c⟩

@[simp] theorem toList_embed (p : GornAddress) : (embed c p).toList = path c ++ p.toList := rfl

@[simp] theorem embed_nil (p : GornAddress) : embed ([] : Context α) p = p := rfl

theorem embed_append (p : GornAddress) : embed (c ++ d) p = embed c (embed d p) :=
  GornAddress.ext (by simp [path_append, List.append_assoc])

/-- Plugging leaves the subtrees of the plugged tree where the embedding carries their
positions. -/
theorem getElem?_plug_embed (p : GornAddress) : (plug c t)[embed c p]? = t[p]? :=
  getElem?_plug_append c t p.toList

variable {c}

/-- A position above an embedded one is above the hole or is itself embedded. -/
theorem le_embed_iff {r p : GornAddress} :
    r ≤ embed c p ↔ r ≤ embed c ⊥ ∨ ∃ q, q ≤ p ∧ embed c q = r := by
  simp only [embed, GornAddress.mulLeft_apply, bot_eq_one, mul_one]
  exact GornAddress.le_mul_iff

/-- The positions below the hole are the embedded ones. -/
theorem embed_bot_le_iff {p : GornAddress} : embed c ⊥ ≤ p ↔ ∃ q, embed c q = p := by
  simp only [embed, GornAddress.mulLeft_apply, bot_eq_one, mul_one]
  exact GornAddress.le_iff_exists_mul.trans (exists_congr fun _ ↦ eq_comm)

/-- The subtree at a position above the hole is the rest of the context, plugged. -/
theorem exists_getElem?_plug_of_le {r : GornAddress} (h : r ≤ embed c ⊥) :
    ∃ c₁ c₂, c₁ ++ c₂ = c ∧ ∀ t : RoseTree α, (plug c t)[r]? = some (plug c₂ t) := by
  obtain ⟨c₁, c₂, rfl, hr⟩ :=
    exists_append_of_prefix_path (c := c) (r := r.toList) (by simpa using GornAddress.le_def.mp h)
  exact ⟨c₁, c₂, rfl, fun t ↦ by
    rw [getElem?_gornAddress, ← hr, plug_append, getElem?_plug_path]⟩

end Context

end RoseTree
