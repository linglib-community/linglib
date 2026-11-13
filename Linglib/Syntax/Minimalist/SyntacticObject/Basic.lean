/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Linglib.Core.Data.Multiset.ZeroCons
public import Linglib.Core.Data.UnorderedTree.Basic
public import Linglib.Core.Data.UnorderedTree.Licensed
public import Linglib.Core.Algebra.FreeCommMagma
public import Linglib.Syntax.Minimalist.LexicalItem

/-!
# Syntactic objects

A syntactic object is a binary rooted tree with leaves labelled by the lexical alphabet and no
labels at internal vertices: an element of the free non-associative commutative magma on `SO₀`.
This file builds two carriers for it over one alphabet of vertices, `Vertex L`, an option of a
leaf label on either side. The left summand is structure: a leaf `Vertex.lex a` of the lexical
alphabet `L`, or the bare label `Vertex.bare` on a binary internal node. The right summand is a
trace: the index-free `Vertex.trace`, or the trace `Vertex.traceOf a` of a label, the cancellation
`T/T_v` remembering the head of `T_v`. Traces are exactly the right summand, the convention of the
trace coproduct. `SyntacticObject L` is the well-formed unordered tree over `Vertex L`, the object
Merge builds, and `PlanarSyntacticObject L` the well-formed ordered tree, the form
linearization produces and PF reads, Marcolli, Chomsky and Berwick's planar embedding.
Well-formedness is a local condition, each vertex licensing its children (`Vertex.Licenses`), so
it descends to the quotient; `PlanarSyntacticObject.toSyntacticObject` forgets the order and
is a homomorphism for the vocabulary the two carriers share, `leaf`, `trace`, `traceOf` and
`merge`.

## Main definitions

* `Minimalist.SyntacticObject.Vertex`, `Minimalist.IsSyntacticObject`
* `Minimalist.SyntacticObject`, `Minimalist.PlanarSyntacticObject`: the unordered and the
  ordered carrier, each with `leaf`, `trace`, `traceOf` and `merge`.
* `Minimalist.PlanarSyntacticObject.toSyntacticObject`: forgetting the order.
* `Minimalist.SyntacticObject.map`, `Minimalist.PlanarSyntacticObject.map`: relabelling along
  a map of lexical alphabets, the induced homomorphism of free commutative magmas.

## Main results

* `Minimalist.SyntacticObject.ind`, `exists_form`: induction and case analysis over the shapes.
* `Minimalist.PlanarSyntacticObject.toSyntacticObject_merge`: forgetting the order commutes
  with Merge.

## Implementation notes

The lexical alphabet `L` defaults to `LexicalItem.Token`, so a bare `SyntacticObject` is the
carrier over tokens; the default pins `L` to `Type`.

## References

* [marcolli-chomsky-berwick-2025], §1.1 (Definition 1.1.1, §1.1.3), §1.2 (Definitions 1.2.1,
  1.2.6) and §1.12
-/

@[expose] public section

namespace Minimalist

open RoseTree UnorderedTree

/-- A vertex carries structure on the left, a leaf of the lexical alphabet `L` or the bare
    internal label, and a trace on the right, index-free or of a label. -/
abbrev SyntacticObject.Vertex (L : Type := LexicalItem.Token) : Type := Option L ⊕ Option L

namespace SyntacticObject

variable {L : Type}

/-- The lexical leaf `a`. -/
@[match_pattern] abbrev Vertex.lex (a : L) : Vertex L := .inl (some a)

/-- The bare label of a binary internal node. -/
@[match_pattern] abbrev Vertex.bare : Vertex L := .inl none

/-- The index-free trace. -/
@[match_pattern] abbrev Vertex.trace : Vertex L := .inr none

/-- The trace of the leaf `a`. -/
@[match_pattern] abbrev Vertex.traceOf (a : L) : Vertex L := .inr (some a)

/-! ### Well-formedness -/

/-- A vertex licenses its children when a lexical leaf or a trace has none and the bare label has
two. -/
def Vertex.Licenses : Vertex L → Multiset (Vertex L) → Prop
  | .inl (some _), ks => ks = 0
  | .inl none, ks => Multiset.card ks = 2
  | .inr _, ks => ks = 0

instance : ∀ (a : Vertex L) (ks : Multiset (Vertex L)), Decidable (Vertex.Licenses a ks)
  | .inl (some _), _ => decidable_of_iff _ Multiset.card_eq_zero
  | .inl none, ks => inferInstanceAs (Decidable (Multiset.card ks = 2))
  | .inr _, _ => decidable_of_iff _ Multiset.card_eq_zero

theorem Vertex.licenses_iff_of_card_eq {a : Vertex L} {ks ls : Multiset (Vertex L)}
    (h : Multiset.card ks = Multiset.card ls) : a.Licenses ks ↔ a.Licenses ls := by
  rcases a with (_ | _) | _ <;>
    simp only [Vertex.Licenses, ← Multiset.card_eq_zero, h]

end SyntacticObject

/-- An unordered tree over `Vertex L` is a syntactic object when every vertex licenses its
    children, so that lexical leaves and traces are leaves and bare vertices are binary. -/
def IsSyntacticObject {L : Type} (t : UnorderedTree (SyntacticObject.Vertex L)) : Prop :=
  t.Licensed SyntacticObject.Vertex.Licenses

instance {L : Type} : DecidablePred (IsSyntacticObject (L := L)) :=
  fun t ↦ inferInstanceAs (Decidable (t.Licensed _))

@[simp] theorem isSyntacticObject_mk {L : Type} (t : RoseTree (SyntacticObject.Vertex L)) :
    IsSyntacticObject (UnorderedTree.mk t) ↔
      t.Licensed fun a ks ↦ SyntacticObject.Vertex.Licenses a (ks : Multiset _) :=
  Iff.rfl

namespace SyntacticObject

variable {L : Type}

theorem isSyntacticObject_mk_leaf {a : Vertex L} (ha : a ≠ Vertex.bare) :
    IsSyntacticObject (UnorderedTree.mk (.node a [])) := by
  refine (isSyntacticObject_mk _).mpr (licensed_node_iff.mpr ⟨?_, by simp⟩)
  match a, ha with
  | .inl (some _), _ | .inr _, _ => rfl
  | .inl none, h => exact absurd rfl h

@[simp] theorem isSyntacticObject_mk_merge (l r : RoseTree (Vertex L)) :
    IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare [l, r])) ↔
      IsSyntacticObject (UnorderedTree.mk l) ∧ IsSyntacticObject (UnorderedTree.mk r) := by
  simp [licensed_node_iff, Vertex.Licenses]

theorem length_eq_zero_or_two {a : Vertex L} {cs : List (RoseTree (Vertex L))}
    (h : IsSyntacticObject (UnorderedTree.mk (.node a cs))) : cs.length = 0 ∨ cs.length = 2 := by
  have h := (licensed_node_iff.mp ((isSyntacticObject_mk _).mp h)).1
  match a with
  | .inl (some _) | .inr _ => exact .inl (by simpa [Vertex.Licenses] using congrArg Multiset.card h)
  | .inl none => exact .inr (by simpa [Vertex.Licenses] using h)

theorem eq_bare_of_ne_nil {a : Vertex L} {cs : List (RoseTree (Vertex L))}
    (h : IsSyntacticObject (UnorderedTree.mk (.node a cs))) (hcs : cs ≠ []) : a = Vertex.bare := by
  have h := (licensed_node_iff.mp ((isSyntacticObject_mk _).mp h)).1
  match a with
  | .inl none => rfl
  | .inl (some _) | .inr _ => exact absurd (by simpa [Vertex.Licenses] using h) hcs

end SyntacticObject

theorem IsSyntacticObject.isFullBinary {L : Type} {t : UnorderedTree (SyntacticObject.Vertex L)}
    (h : IsSyntacticObject t) : t.IsFullBinary :=
  UnorderedTree.Licensed.mono (R := SyntacticObject.Vertex.Licenses) (fun
    | .inl (some _), _, h | .inr _, _, h => .inl (congrArg Multiset.card h)
    | .inl none, _, h => .inr h) h

/-! ### Leaves and the two carriers -/

namespace SyntacticObject

variable {L L' L'' : Type}

/-- A leaf of a syntactic object: a lexical item, the index-free trace, or the trace of an item. -/
inductive Leaf (L : Type) where
  /-- A lexical item. -/
  | lex (a : L)
  /-- The index-free trace. -/
  | trace
  /-- The trace of the item `a`. -/
  | traceOf (a : L)
  deriving DecidableEq

namespace Leaf

/-- The vertex a leaf labels. -/
def toVertex : Leaf L → Vertex L
  | lex a => Vertex.lex a
  | trace => Vertex.trace
  | traceOf a => Vertex.traceOf a

theorem toVertex_injective : Function.Injective (toVertex (L := L)) := by
  rintro (a | _ | a) (b | _ | b) h <;> simp_all [toVertex]

theorem toVertex_ne_bare (x : Leaf L) : x.toVertex ≠ Vertex.bare := by
  cases x <;> simp [toVertex]

/-- The leaf with its item relabelled by `f`. -/
def map (f : L → L') : Leaf L → Leaf L'
  | lex a => lex (f a)
  | trace => trace
  | traceOf a => traceOf (f a)

@[simp] theorem map_id : map (id : L → L) = id := by funext x; cases x <;> rfl

theorem map_comp (f : L → L') (g : L' → L'') : map g ∘ map f = map (g ∘ f) := by
  funext x; cases x <;> rfl

end Leaf

end SyntacticObject

/-- The planar syntactic objects over `L`, the free magma on the leaves:
[marcolli-chomsky-berwick-2025] §1.12's planar syntactic objects. -/
abbrev PlanarSyntacticObject (L : Type := LexicalItem.Token) : Type :=
  FreeMagma (SyntacticObject.Leaf L)

/-- The syntactic objects over `L`, the free commutative magma on the leaves. -/
abbrev SyntacticObject (L : Type := LexicalItem.Token) : Type :=
  FreeCommMagma (SyntacticObject.Leaf L)

/-! ### Planar objects -/

namespace PlanarSyntacticObject

open SyntacticObject (Vertex Leaf isSyntacticObject_mk_leaf isSyntacticObject_mk_merge)

variable {L : Type}

/-- A lexical leaf. -/
@[coe] def leaf (a : L) : PlanarSyntacticObject L := FreeMagma.of (.lex a)

/-- The index-free trace. -/
def trace : PlanarSyntacticObject L := FreeMagma.of .trace

/-- The trace of `a`. -/
def traceOf (a : L) : PlanarSyntacticObject L := FreeMagma.of (.traceOf a)

/-- Merge, with the daughters in the given order, also written `*`. -/
abbrev merge (l r : PlanarSyntacticObject L) : PlanarSyntacticObject L := l * r

/-- The ordered tree of a planar object. -/
def toRoseTree : PlanarSyntacticObject L → RoseTree (Vertex L)
  | .of x => .node x.toVertex []
  | .mul l r => .node Vertex.bare [toRoseTree l, toRoseTree r]

@[simp] theorem toRoseTree_leaf (a : L) :
    (leaf a).toRoseTree = .node (Vertex.lex a) [] := rfl
@[simp] theorem toRoseTree_trace : (trace : PlanarSyntacticObject L).toRoseTree =
    .node Vertex.trace [] :=
  rfl
@[simp] theorem toRoseTree_traceOf (a : L) :
    (traceOf a).toRoseTree = .node (Vertex.traceOf a) [] :=
  rfl
@[simp] theorem toRoseTree_merge (l r : PlanarSyntacticObject L) :
    (merge l r).toRoseTree = .node Vertex.bare [l.toRoseTree, r.toRoseTree] := rfl

/-- The tree of a planar object is well formed. -/
theorem isSyntacticObject_toRoseTree (p : PlanarSyntacticObject L) :
    IsSyntacticObject (UnorderedTree.mk p.toRoseTree) := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => exact isSyntacticObject_mk_leaf x.toVertex_ne_bare
  | ih2 l r hl hr => exact (isSyntacticObject_mk_merge _ _).2 ⟨hl, hr⟩

theorem toRoseTree_injective : Function.Injective (toRoseTree : PlanarSyntacticObject L → _) := by
  intro p
  induction p using FreeMagma.recOnMul with
  | ih1 x =>
    intro q h
    cases q with
    | of y => exact congrArg FreeMagma.of (Leaf.toVertex_injective (by simpa [toRoseTree] using h))
    | mul l r => simp [toRoseTree] at h
  | ih2 l r hl hr =>
    intro q h
    cases q with
    | of y => simp [toRoseTree] at h
    | mul l' r' =>
      obtain ⟨h₁, h₂⟩ : toRoseTree l = toRoseTree l' ∧ toRoseTree r = toRoseTree r' := by
          simpa [toRoseTree] using h
      rw [hl h₁, hr h₂]; rfl

/-- Forgetting the order is the quotient map to the syntactic object. -/
@[coe] def toSyntacticObject (p : PlanarSyntacticObject L) : SyntacticObject L :=
  FreeMagma.toFreeCommMagma p

theorem toSyntacticObject_surjective :
    Function.Surjective (toSyntacticObject : PlanarSyntacticObject L → SyntacticObject L) :=
  FreeMagma.toFreeCommMagma_surjective

/-- Two planar objects with one syntactic object have one unordered tree. -/
theorem mk_toRoseTree_eq_of_commCon {p q : PlanarSyntacticObject L}
    (h : Magma.commCon (FreeMagma (Leaf L)) p q) :
    UnorderedTree.mk p.toRoseTree = UnorderedTree.mk q.toRoseTree := by
  induction h with
  | of x y h =>
    obtain ⟨a, b, rfl, rfl⟩ := h
    show UnorderedTree.mk (.node Vertex.bare [toRoseTree a, toRoseTree b])
      = UnorderedTree.mk (.node Vertex.bare [toRoseTree b, toRoseTree a])
    rw [← UnorderedTree.node_pair_mk, ← UnorderedTree.node_pair_mk, Multiset.pair_comm]
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | @mul w x y z _ _ ih₁ ih₂ =>
    show UnorderedTree.mk (.node Vertex.bare [toRoseTree w, toRoseTree y])
      = UnorderedTree.mk (.node Vertex.bare [toRoseTree x, toRoseTree z])
    rw [← UnorderedTree.node_pair_mk, ← UnorderedTree.node_pair_mk, ih₁, ih₂]

end PlanarSyntacticObject

/-! ### The shapes -/

namespace SyntacticObject

variable {L : Type}

/-- A lexical leaf. -/
@[coe] def leaf (a : L) : SyntacticObject L := FreeCommMagma.of (.lex a)

/-- The index-free trace, the mark an admissible cut leaves in the remaining tree
    ([marcolli-chomsky-berwick-2025], Definition 1.2.6); `traceOf` is the indexed trace. -/
def trace : SyntacticObject L := FreeCommMagma.of .trace

/-- The trace of `a`. -/
def traceOf (a : L) : SyntacticObject L := FreeCommMagma.of (.traceOf a)

/-- Merge on the carrier, the product of the free commutative magma, also written `*`. -/
abbrev merge (l r : SyntacticObject L) : SyntacticObject L := l * r

/-- The unordered tree of a syntactic object. -/
def toUnorderedTree (s : SyntacticObject L) : UnorderedTree (Vertex L) :=
  Quotient.liftOn s (fun p : PlanarSyntacticObject L ↦ UnorderedTree.mk p.toRoseTree)
    fun _ _ h ↦ PlanarSyntacticObject.mk_toRoseTree_eq_of_commCon h

@[simp] theorem _root_.Minimalist.PlanarSyntacticObject.toUnorderedTree_toSyntacticObject
    (p : PlanarSyntacticObject L) : p.toSyntacticObject.toUnorderedTree =
        UnorderedTree.mk p.toRoseTree := rfl

@[simp] theorem toUnorderedTree_leaf (a : L) :
    (leaf a).toUnorderedTree = UnorderedTree.leaf (Vertex.lex a) :=
  rfl
@[simp] theorem toUnorderedTree_trace : (trace : SyntacticObject L).toUnorderedTree =
    UnorderedTree.leaf Vertex.trace :=
  rfl
@[simp] theorem toUnorderedTree_traceOf (a : L) :
    (traceOf a).toUnorderedTree = UnorderedTree.leaf (Vertex.traceOf a) := rfl

theorem isSyntacticObject_merge_iff (a b : UnorderedTree (Vertex L)) :
    IsSyntacticObject (UnorderedTree.node Vertex.bare {a, b}) ↔
      IsSyntacticObject a ∧ IsSyntacticObject b := by
  refine Quotient.inductionOn₂ a b fun pa pb ↦ ?_
  show IsSyntacticObject (UnorderedTree.node Vertex.bare {UnorderedTree.mk pa,
    UnorderedTree.mk pb}) ↔
    IsSyntacticObject (UnorderedTree.mk pa) ∧ IsSyntacticObject (UnorderedTree.mk pb)
  rw [show ({UnorderedTree.mk pa, UnorderedTree.mk pb} : Multiset (UnorderedTree (Vertex L)))
        = Multiset.ofList ([pa, pb].map UnorderedTree.mk) from rfl, UnorderedTree.node_mk_tree_list]
  exact isSyntacticObject_mk_merge pa pb

@[simp] theorem toUnorderedTree_merge (l r : SyntacticObject L) :
    (merge l r).toUnorderedTree = UnorderedTree.node Vertex.bare {l.toUnorderedTree,
        r.toUnorderedTree} := by
  obtain ⟨l, rfl⟩ := PlanarSyntacticObject.toSyntacticObject_surjective l
  obtain ⟨r, rfl⟩ := PlanarSyntacticObject.toSyntacticObject_surjective r
  exact (UnorderedTree.node_pair_mk _ _ _).symm

/-- The tree of a syntactic object is well formed. -/
theorem isSyntacticObject_toUnorderedTree (s : SyntacticObject L) :
    IsSyntacticObject s.toUnorderedTree := by
  obtain ⟨p, rfl⟩ := PlanarSyntacticObject.toSyntacticObject_surjective s
  exact p.isSyntacticObject_toRoseTree

@[simp] theorem leaf_inj {a b : L} : leaf a = leaf b ↔ a = b :=
  ⟨fun h ↦ by injection FreeCommMagma.of_injective h, congrArg leaf⟩

theorem merge_comm (l r : SyntacticObject L) : merge l r = merge r l := mul_comm l r

theorem merge_eq_merge_iff {l r l' r' : SyntacticObject L} :
    merge l r = merge l' r' ↔ l = l' ∧ r = r' ∨ l = r' ∧ r = l' :=
  FreeCommMagma.mul_eq_mul_iff

@[simp]
theorem leaf_ne_merge (a : L) (l r : SyntacticObject L) : leaf a ≠ merge l r :=
  FreeCommMagma.of_ne_mul _ l r

@[simp]
theorem leaf_ne_trace (a : L) : leaf a ≠ trace :=
  fun h ↦ by injection FreeCommMagma.of_injective h

@[simp]
theorem leaf_ne_traceOf (a b : L) : leaf a ≠ traceOf b :=
  fun h ↦ by injection FreeCommMagma.of_injective h

@[simp]
theorem traceOf_ne_merge (a : L) (l r : SyntacticObject L) :
    traceOf a ≠ merge l r :=
  FreeCommMagma.of_ne_mul _ l r

@[simp]
theorem traceOf_ne_leaf (a b : L) : traceOf a ≠ leaf b :=
  fun h ↦ by injection FreeCommMagma.of_injective h

@[simp] theorem traceOf_inj {a b : L} : traceOf a = traceOf b ↔ a = b :=
  ⟨fun h ↦ by injection FreeCommMagma.of_injective h, congrArg traceOf⟩

@[simp]
theorem trace_ne_merge (l r : SyntacticObject L) : (trace : SyntacticObject L) ≠ merge l r :=
  FreeCommMagma.of_ne_mul _ l r

end SyntacticObject

namespace PlanarSyntacticObject

variable {L : Type}

@[simp] theorem toSyntacticObject_leaf (a : L) :
    (leaf a).toSyntacticObject = SyntacticObject.leaf a := rfl

@[simp] theorem toSyntacticObject_trace :
    (trace : PlanarSyntacticObject L).toSyntacticObject = SyntacticObject.trace := rfl

@[simp] theorem toSyntacticObject_traceOf (a : L) :
    (traceOf a).toSyntacticObject = SyntacticObject.traceOf a := rfl

/-- Forgetting the order commutes with Merge. -/
@[simp] theorem toSyntacticObject_merge (l r : PlanarSyntacticObject L) :
    (merge l r).toSyntacticObject = SyntacticObject.merge l.toSyntacticObject r.toSyntacticObject :=
  map_mul FreeMagma.toFreeCommMagma l r

end PlanarSyntacticObject

/-! ### Induction and case analysis -/

namespace SyntacticObject

variable {L : Type}

/-- Induction on syntactic objects, each of which is a lexical leaf, a trace, or the Merge of two
    syntactic objects. -/
@[elab_as_elim]
theorem ind {motive : SyntacticObject L → Prop}
    (leaf : ∀ a, motive (leaf a)) (trace : motive trace)
    (traceOf : ∀ a, motive (traceOf a))
    (merge : ∀ l r, motive l → motive r → motive (merge l r)) (s : SyntacticObject L) :
    motive s := by
  induction s using FreeCommMagma.inductionOn with
  | of x => cases x with
    | lex a => exact leaf a
    | trace => exact trace
    | traceOf a => exact traceOf a
  | mul x y hx hy => exact merge x y hx hy

/-- A syntactic object is a lexical leaf, a trace, or a Merge. -/
theorem exists_form (s : SyntacticObject L) :
    (∃ a, s = leaf a) ∨ s = trace ∨ (∃ a, s = traceOf a) ∨ (∃ l r, s = merge l r) := by
  induction s using ind with
  | leaf a => exact Or.inl ⟨a, rfl⟩
  | trace => exact Or.inr (Or.inl rfl)
  | traceOf a => exact Or.inr (Or.inr (Or.inl ⟨a, rfl⟩))
  | merge l r _ _ => exact Or.inr (Or.inr (Or.inr ⟨l, r, rfl⟩))

/-- A syntactic object is determined by its tree. -/
theorem toUnorderedTree_injective : Function.Injective (toUnorderedTree : SyntacticObject L → _) :=
    by
  intro s
  induction s using ind with
  | leaf a =>
    intro t h
    rcases exists_form t with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      simpa using congrArg UnorderedTree.value h
  | trace =>
    intro t h
    rcases exists_form t with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      first | rfl | simpa using congrArg UnorderedTree.value h
  | traceOf a =>
    intro t h
    rcases exists_form t with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l, r, rfl⟩ <;>
      simpa using congrArg UnorderedTree.value h
  | merge l r hl hr =>
    intro t h
    rcases exists_form t with ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩ | ⟨l', r', rfl⟩
    iterate 3 simpa using congrArg UnorderedTree.value h
    have := congrArg UnorderedTree.children h
    simp only [toUnorderedTree_merge, UnorderedTree.children_node] at this
    rcases Multiset.pair_eq_pair_iff.1 this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [hl h₁, hr h₂]
    · rw [hl h₁, hr h₂]; exact merge_comm _ _

@[simp] theorem toUnorderedTree_inj {s t : SyntacticObject L} : s.toUnorderedTree =
    t.toUnorderedTree ↔ s = t := toUnorderedTree_injective.eq_iff

end SyntacticObject

/-! ### Objects from trees -/

namespace PlanarSyntacticObject

open SyntacticObject (Vertex Leaf length_eq_zero_or_two eq_bare_of_ne_nil
  isSyntacticObject_mk_merge)

variable {L : Type}

/-- One step of reading a planar object off a tree: a lexical or trace vertex without
daughters is a leaf, and a bare vertex over two objects is their Merge. -/
def ofRoseTreeStep : Vertex L → List (Option (PlanarSyntacticObject L)) →
    Option (PlanarSyntacticObject L)
  | .inl (some a), [] => some (leaf a)
  | .inr none, [] => some trace
  | .inr (some a), [] => some (traceOf a)
  | .inl none, [some l, some r] => some (l * r)
  | _, _ => none

/-- The planar object with a given tree, if the tree is well formed. -/
def ofRoseTree? : RoseTree (Vertex L) → Option (PlanarSyntacticObject L) :=
  RoseTree.fold ofRoseTreeStep

theorem ofRoseTree?_node (a : Vertex L) (cs : List (RoseTree (Vertex L))) :
    ofRoseTree? (.node a cs) = ofRoseTreeStep a (cs.map ofRoseTree?) :=
  RoseTree.fold_node _ _ _

@[simp] theorem ofRoseTree?_toRoseTree (p : PlanarSyntacticObject L) : ofRoseTree? p.toRoseTree =
    some p := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => cases x <;> rfl
  | ih2 l r hl hr =>
    show ofRoseTree? (.node Vertex.bare [toRoseTree l, toRoseTree r]) = some (l * r)
    rw [ofRoseTree?_node, List.map_cons, List.map_cons, List.map_nil, hl, hr]
    rfl

/-- A well-formed tree is the tree of a planar object. -/
theorem exists_toRoseTree_eq {t : RoseTree (Vertex L)} (h : IsSyntacticObject (UnorderedTree.mk
    t)) :
    ∃ p : PlanarSyntacticObject L, p.toRoseTree = t := by
  induction t with
  | node lbl cs ih =>
    rcases length_eq_zero_or_two h with hlen | hlen
    · obtain rfl := List.length_eq_zero_iff.mp hlen
      rcases lbl with (_ | a) | (_ | a)
      · exact absurd (RoseTree.licensed_node_iff.mp ((isSyntacticObject_mk _).mp h)).1
          (by simp [Vertex.Licenses])
      · exact ⟨leaf a, rfl⟩
      · exact ⟨trace, rfl⟩
      · exact ⟨traceOf a, rfl⟩
    · obtain ⟨pl, pr, rfl⟩ := List.length_eq_two.mp hlen
      obtain rfl := eq_bare_of_ne_nil h (by simp)
      obtain ⟨hl, hr⟩ := (isSyntacticObject_mk_merge pl pr).mp h
      obtain ⟨l, rfl⟩ := ih pl (by simp) hl
      obtain ⟨r, rfl⟩ := ih pr (by simp) hr
      exact ⟨l * r, rfl⟩

/-- The planar object with the well-formed tree `t`. -/
def ofRoseTree (t : RoseTree (Vertex L)) (_h : IsSyntacticObject (UnorderedTree.mk t)) :
    PlanarSyntacticObject L :=
  (ofRoseTree? t).getD trace

@[simp] theorem toRoseTree_ofRoseTree (t : RoseTree (Vertex L)) (h : IsSyntacticObject
    (UnorderedTree.mk t)) :
    (ofRoseTree t h).toRoseTree = t := by
  obtain ⟨p, rfl⟩ := exists_toRoseTree_eq h
  rw [ofRoseTree, ofRoseTree?_toRoseTree, Option.getD_some]

@[simp] theorem ofRoseTree_toRoseTree (p : PlanarSyntacticObject L) :
    ofRoseTree p.toRoseTree p.isSyntacticObject_toRoseTree = p :=
  toRoseTree_injective (toRoseTree_ofRoseTree _ _)

theorem ofRoseTree_node_bare (u v : RoseTree (Vertex L))
    (h : IsSyntacticObject (UnorderedTree.mk (.node Vertex.bare [u, v]))) :
    ofRoseTree (.node Vertex.bare [u, v]) h =
      merge (ofRoseTree u ((isSyntacticObject_mk_merge u v).1 h).1)
        (ofRoseTree v ((isSyntacticObject_mk_merge u v).1 h).2) :=
  toRoseTree_injective (by simp)

/-- Every planar object is the object of its tree. -/
theorem exists_eq_ofRoseTree (p : PlanarSyntacticObject L) : ∃ t h, p = ofRoseTree t h :=
  ⟨p.toRoseTree, p.isSyntacticObject_toRoseTree, (ofRoseTree_toRoseTree p).symm⟩

end PlanarSyntacticObject

namespace SyntacticObject

variable {L : Type}

/-- The syntactic object with the well-formed tree `t`. -/
def ofUnorderedTree (t : UnorderedTree (Vertex L)) (_h : IsSyntacticObject t) : SyntacticObject L :=
  Quotient.liftOn t
    (fun r ↦ if h : IsSyntacticObject (UnorderedTree.mk r) then
      (PlanarSyntacticObject.ofRoseTree r h).toSyntacticObject else trace)
    fun r r' hr ↦ by
      have hmk : UnorderedTree.mk r = UnorderedTree.mk r' := Quotient.sound hr
      by_cases h : IsSyntacticObject (UnorderedTree.mk r)
      · have h' : IsSyntacticObject (UnorderedTree.mk r') := hmk ▸ h
        simp only [h, h', ↓reduceDIte]
        refine toUnorderedTree_injective ?_
        rw [PlanarSyntacticObject.toUnorderedTree_toSyntacticObject,
          PlanarSyntacticObject.toUnorderedTree_toSyntacticObject,
              PlanarSyntacticObject.toRoseTree_ofRoseTree,
          PlanarSyntacticObject.toRoseTree_ofRoseTree, hmk]
      · have h' : ¬ IsSyntacticObject (UnorderedTree.mk r') := hmk ▸ h
        simp only [h, h', ↓reduceDIte]

@[simp] theorem toUnorderedTree_ofUnorderedTree (t : UnorderedTree (Vertex L)) (h :
    IsSyntacticObject t) :
    (ofUnorderedTree t h).toUnorderedTree = t := by
  induction t using Quotient.inductionOn with
  | _ r =>
    show (if h : IsSyntacticObject (UnorderedTree.mk r) then
      (PlanarSyntacticObject.ofRoseTree r h).toSyntacticObject else trace).toUnorderedTree =
          UnorderedTree.mk r
    have h' : IsSyntacticObject (UnorderedTree.mk r) := h
    simp only [h', ↓reduceDIte, PlanarSyntacticObject.toUnorderedTree_toSyntacticObject,
      PlanarSyntacticObject.toRoseTree_ofRoseTree]

@[simp] theorem ofUnorderedTree_toUnorderedTree (s : SyntacticObject L) :
    ofUnorderedTree s.toUnorderedTree s.isSyntacticObject_toUnorderedTree = s :=
  toUnorderedTree_injective (toUnorderedTree_ofUnorderedTree _ _)

@[simp] theorem _root_.Minimalist.PlanarSyntacticObject.toSyntacticObject_ofRoseTree
    (t : RoseTree (Vertex L)) (h : IsSyntacticObject (UnorderedTree.mk t)) :
    (PlanarSyntacticObject.ofRoseTree t h).toSyntacticObject = ofUnorderedTree (UnorderedTree.mk
        t) h :=
  toUnorderedTree_injective (by simp)

/-- Syntactic objects are the well-formed unordered trees. -/
def unorderedTreeEquiv : SyntacticObject L ≃ {t : UnorderedTree (Vertex L) // IsSyntacticObject
    t} where
  toFun s := ⟨s.toUnorderedTree, s.isSyntacticObject_toUnorderedTree⟩
  invFun t := ofUnorderedTree t.1 t.2
  left_inv := ofUnorderedTree_toUnorderedTree
  right_inv t := Subtype.ext (toUnorderedTree_ofUnorderedTree t.1 t.2)

end SyntacticObject


/-! ### Functoriality -/

namespace SyntacticObject

variable {L L' L'' : Type}

/-- The vertex with its label relabelled by `f`. -/
def Vertex.map (f : L → L') : Vertex L → Vertex L' := Sum.map (Option.map f) (Option.map f)

@[simp] theorem Vertex.map_lex (f : L → L') (a : L) :
    (Vertex.lex a).map f = Vertex.lex (f a) := rfl

@[simp] theorem Vertex.map_bare (f : L → L') : (Vertex.bare : Vertex L).map f = Vertex.bare := rfl

@[simp] theorem Vertex.map_trace (f : L → L') :
    (Vertex.trace : Vertex L).map f = Vertex.trace := rfl

@[simp] theorem Vertex.map_traceOf (f : L → L') (a : L) :
    (Vertex.traceOf a).map f = Vertex.traceOf (f a) := rfl

@[simp] theorem Vertex.map_id : Vertex.map (id : L → L) = id := by
  funext v; rcases v with (_ | _) | (_ | _) <;> rfl

theorem Vertex.map_comp (f : L → L') (g : L' → L'') :
    Vertex.map g ∘ Vertex.map f = Vertex.map (g ∘ f) := by
  funext v; rcases v with (_ | _) | (_ | _) <;> rfl

theorem Vertex.map_injective {f : L → L'} (hf : Function.Injective f) :
    Function.Injective (Vertex.map f) :=
  Sum.map_injective.2 ⟨Option.map_injective hf, Option.map_injective hf⟩

theorem Vertex.licenses_map_iff (f : L → L') (a : Vertex L) (ks : List (Vertex L)) :
    (a.map f).Licenses (ks.map (Vertex.map f) : Multiset _) ↔ a.Licenses ks := by
  rcases a with (_ | _) | _ <;> simp [Vertex.map, Vertex.Licenses]

end SyntacticObject

theorem isSyntacticObject_map_iff {L L' : Type} (f : L → L')
    (t : UnorderedTree (SyntacticObject.Vertex L)) :
    IsSyntacticObject (t.map (SyntacticObject.Vertex.map f)) ↔ IsSyntacticObject t := by
  refine Quotient.inductionOn t fun p ↦ ?_
  show IsSyntacticObject ((UnorderedTree.mk p).map _) ↔ IsSyntacticObject (UnorderedTree.mk p)
  rw [UnorderedTree.map_mk, isSyntacticObject_mk, isSyntacticObject_mk]
  exact RoseTree.licensed_map_iff (SyntacticObject.Vertex.licenses_map_iff f)


namespace SyntacticObject

variable {L L' L'' : Type}

theorem Leaf.toVertex_map (f : L → L') (x : Leaf L) :
    (x.map f).toVertex = Vertex.map f x.toVertex := by
  cases x <;> rfl

end SyntacticObject

namespace PlanarSyntacticObject

open SyntacticObject (Vertex Leaf)

variable {L L' L'' : Type}

/-- The planar object with its labels relabelled by `f`. -/
def map (f : L → L') (p : PlanarSyntacticObject L) : PlanarSyntacticObject L' :=
  FreeMagma.map (Leaf.map f) p

@[simp] theorem toRoseTree_map (f : L → L') (p : PlanarSyntacticObject L) :
    (p.map f).toRoseTree = p.toRoseTree.map (Vertex.map f) := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => simp [map, toRoseTree, Leaf.toVertex_map]
  | ih2 l r hl hr =>
    have hl' : toRoseTree (FreeMagma.map (Leaf.map f) l) = RoseTree.map (Vertex.map f) (toRoseTree
        l) := hl
    have hr' : toRoseTree (FreeMagma.map (Leaf.map f) r) = RoseTree.map (Vertex.map f) (toRoseTree
        r) := hr
    simp [map, toRoseTree, hl', hr']

@[simp] theorem map_leaf (f : L → L') (a : L) : (leaf a).map f = leaf (f a) := rfl

@[simp] theorem map_trace (f : L → L') : (trace : PlanarSyntacticObject L).map f = trace := rfl

@[simp] theorem map_traceOf (f : L → L') (a : L) : (traceOf a).map f = traceOf (f a) := rfl

@[simp] theorem map_merge (f : L → L') (l r : PlanarSyntacticObject L) :
    (merge l r).map f = merge (l.map f) (r.map f) := rfl

@[simp] theorem map_id (p : PlanarSyntacticObject L) : p.map id = p :=
  toRoseTree_injective (by rw [toRoseTree_map, Vertex.map_id, RoseTree.map_id])

@[simp] theorem map_map (f : L → L') (g : L' → L'') (p : PlanarSyntacticObject L) :
    (p.map f).map g = p.map (g ∘ f) :=
  toRoseTree_injective (by rw [toRoseTree_map, toRoseTree_map, toRoseTree_map, RoseTree.map_map,
      Vertex.map_comp])

theorem map_injective {f : L → L'} (hf : Function.Injective f) :
    Function.Injective (map f : PlanarSyntacticObject L → PlanarSyntacticObject L') :=
  fun p q h ↦ toRoseTree_injective (RoseTree.map_injective (Vertex.map_injective hf)
    (by rw [← toRoseTree_map, ← toRoseTree_map, h]))

end PlanarSyntacticObject

namespace SyntacticObject

variable {L L' L'' : Type}

/-- The syntactic object with its labels relabelled by `f`, the homomorphism of free commutative
magmas that a map of lexical alphabets induces. -/
def map (f : L → L') (s : SyntacticObject L) : SyntacticObject L' :=
  FreeCommMagma.map (Leaf.map f) s

@[simp] theorem _root_.Minimalist.PlanarSyntacticObject.toSyntacticObject_map (f : L → L')
    (p : PlanarSyntacticObject L) :
    (p.map f).toSyntacticObject = p.toSyntacticObject.map f := by
  induction p using FreeMagma.recOnMul with
  | ih1 x => rfl
  | ih2 l r hl hr =>
    show FreeMagma.toFreeCommMagma (FreeMagma.map (Leaf.map f) (l * r))
      = FreeCommMagma.map (Leaf.map f) (FreeMagma.toFreeCommMagma (l * r))
    rw [map_mul, map_mul, map_mul, map_mul]
    exact congrArg₂ (· * ·) hl hr

@[simp] theorem toUnorderedTree_map (f : L → L') (s : SyntacticObject L) :
    (s.map f).toUnorderedTree = s.toUnorderedTree.map (Vertex.map f) := by
  obtain ⟨p, rfl⟩ := PlanarSyntacticObject.toSyntacticObject_surjective s
  rw [← PlanarSyntacticObject.toSyntacticObject_map,
    PlanarSyntacticObject.toUnorderedTree_toSyntacticObject, PlanarSyntacticObject.toRoseTree_map,
    PlanarSyntacticObject.toUnorderedTree_toSyntacticObject, UnorderedTree.map_mk]

@[simp] theorem map_leaf (f : L → L') (a : L) : (leaf a).map f = leaf (f a) := rfl

@[simp] theorem map_trace (f : L → L') : (trace : SyntacticObject L).map f = trace := rfl

@[simp] theorem map_traceOf (f : L → L') (a : L) : (traceOf a).map f = traceOf (f a) := rfl

@[simp] theorem map_merge (f : L → L') (l r : SyntacticObject L) :
    (merge l r).map f = merge (l.map f) (r.map f) :=
  map_mul (FreeCommMagma.map (Leaf.map f)) l r

@[simp] theorem map_id (s : SyntacticObject L) : s.map id = s :=
  toUnorderedTree_injective (by rw [toUnorderedTree_map, Vertex.map_id, UnorderedTree.map_id])

@[simp] theorem map_map (f : L → L') (g : L' → L'') (s : SyntacticObject L) :
    (s.map f).map g = s.map (g ∘ f) :=
  toUnorderedTree_injective (by rw [toUnorderedTree_map, toUnorderedTree_map, toUnorderedTree_map,
      UnorderedTree.map_map, Vertex.map_comp])

theorem map_injective {f : L → L'} (hf : Function.Injective f) :
    Function.Injective (map f : SyntacticObject L → SyntacticObject L') :=
  fun s t h ↦ toUnorderedTree_injective (UnorderedTree.map_injective (Vertex.map_injective hf)
    (by rw [← toUnorderedTree_map, ← toUnorderedTree_map, h]))

end SyntacticObject

end Minimalist
