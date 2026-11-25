/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Algebra.FreeCommMagma
public import Linglib.Core.Data.RoseTree.Positions
public import Linglib.Core.Data.UnorderedTree.Basic

/-!
# Syntactic objects

A syntactic object over a type `α` of lexical items is a lexical item or the Merge of two
syntactic objects. With no order on the two, the syntactic objects are the free commutative magma
on `α` and Merge is its product, as in [marcolli-chomsky-berwick-2025] and
[collins-stabler-2016]. A planar syntactic object orders the daughters of every Merge.

The terms of an object are the objects reached from it through daughters. A planar object has a
tree, whose leaves carry the lexical items, and the object at each position of that tree is a
term. Dominance, lowest common ancestors and command between positions are those of the tree.
Two positions that hold the same object are copies of one element.

## Main definitions

* `Minimalist.Next.SyntacticObject`, `Minimalist.Next.PlanarSyntacticObject`.
* `Minimalist.Next.SyntacticObject.terms`, `Minimalist.Next.SyntacticObject.yield`.
* `Minimalist.Next.PlanarSyntacticObject.toRoseTree`,
  `Minimalist.Next.SyntacticObject.toUnorderedTree`: the tree of an object.
* `Minimalist.Next.PlanarSyntacticObject.termAt`, `Minimalist.Next.PlanarSyntacticObject.chain`:
  the object at a position, and the positions that hold one object.

## Main results

* `Minimalist.Next.SyntacticObject.mem_terms`: the terms are what is reached through daughters.
* `Minimalist.Next.PlanarSyntacticObject.mem_terms_iff_exists_termAt`: the terms of an object are
  the objects at the positions of a planar form of it.
* `Minimalist.Next.SyntacticObject.toUnorderedTree_coe`: the tree of an object is the tree of a
  planar form of it, with the order of daughters forgotten.

## Implementation notes

* The lexical items are a parameter and nothing is assumed of them. Tokens, single features, and
  items together with the traces of an account that leaves traces are choices of `α`.
* An object maps to a tree and no tree is mapped back. What is proved of the positions of a rose
  tree applies to the positions of `toRoseTree`.
* Objects are values, so an element merged again with an object that contains it is one term at
  two positions.

## References

* [marcolli-chomsky-berwick-2025]
* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist.Next

variable {α β : Type*}

/-- The syntactic objects over the lexical items `α`: the free commutative magma on `α`, with
Merge its product. -/
abbrev SyntacticObject (α : Type*) : Type _ := FreeCommMagma α

/-- A syntactic object with its daughters in an order. -/
abbrev PlanarSyntacticObject (α : Type*) : Type _ := FreeMagma α

namespace SyntacticObject

/-- A lexical item as an object. -/
abbrev leaf (a : α) : SyntacticObject α := FreeCommMagma.of a

/-! ### Terms -/

/-- `y` is a daughter of `x`: `x` is the Merge of `y` with something. -/
def IsDaughter (y x : SyntacticObject α) : Prop := ∃ z, x = y * z

/-- `x` contains `y`: `y` is reached from `x` through daughters. -/
def Contains (x y : SyntacticObject α) : Prop := Relation.TransGen IsDaughter y x

/-- The terms of an object, itself included, one for each place a term occurs. -/
def terms : SyntacticObject α → Multiset (SyntacticObject α) :=
  FreeCommMagma.elim (fun a ↦ {leaf a}) (fun l r a b ↦ (l * r) ::ₘ (a + b))
    fun l r a b ↦ by rw [mul_comm, add_comm]

@[simp] theorem terms_leaf (a : α) : (leaf a).terms = {leaf a} := rfl

@[simp] theorem terms_mul (l r : SyntacticObject α) :
    (l * r).terms = (l * r) ::ₘ (l.terms + r.terms) :=
  FreeCommMagma.elim_mul _ _ _ l r

theorem not_isDaughter_leaf (y : SyntacticObject α) (a : α) : ¬ IsDaughter y (leaf a) :=
  fun ⟨z, h⟩ ↦ FreeCommMagma.of_ne_mul a y z h

theorem isDaughter_mul {y l r : SyntacticObject α} : IsDaughter y (l * r) ↔ y = l ∨ y = r := by
  refine ⟨fun ⟨z, h⟩ ↦ ?_, ?_⟩
  · rcases FreeCommMagma.mul_eq_mul_iff.1 h with ⟨h, -⟩ | ⟨-, h⟩
    · exact .inl h.symm
    · exact .inr h.symm
  · rintro (rfl | rfl)
    · exact ⟨r, rfl⟩
    · exact ⟨l, mul_comm l y⟩

theorem mem_terms {x y : SyntacticObject α} :
    y ∈ x.terms ↔ Relation.ReflTransGen IsDaughter y x := by
  induction x using FreeCommMagma.inductionOn with
  | of a =>
    rw [terms_leaf, Multiset.mem_singleton]
    refine ⟨fun h ↦ h ▸ .refl, fun h ↦ ?_⟩
    rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, -, hc⟩
    · exact h.symm
    · exact absurd hc (not_isDaughter_leaf c a)
  | mul l r ihl ihr =>
    rw [terms_mul, Multiset.mem_cons, Multiset.mem_add, ihl, ihr]
    constructor
    · rintro (rfl | h | h)
      · exact .refl
      · exact h.tail (isDaughter_mul.2 (.inl rfl))
      · exact h.tail (isDaughter_mul.2 (.inr rfl))
    · intro h
      rcases Relation.ReflTransGen.cases_tail h with h | ⟨c, hc, hd⟩
      · exact .inl h.symm
      · rcases isDaughter_mul.1 hd with rfl | rfl
        · exact .inr (.inl hc)
        · exact .inr (.inr hc)

/-- `x` contains `y` or is `y`. -/
def ContainsOrEq (x y : SyntacticObject α) : Prop := Relation.ReflTransGen IsDaughter y x

theorem mem_terms_iff_containsOrEq {x y : SyntacticObject α} : y ∈ x.terms ↔ ContainsOrEq x y :=
  mem_terms

instance [DecidableEq α] (x y : SyntacticObject α) : Decidable (ContainsOrEq x y) :=
  decidable_of_iff _ mem_terms_iff_containsOrEq

@[simp] theorem containsOrEq_refl (x : SyntacticObject α) : ContainsOrEq x x := .refl

theorem ContainsOrEq.trans {x y z : SyntacticObject α} (hxy : ContainsOrEq x y)
    (hyz : ContainsOrEq y z) : ContainsOrEq x z :=
  Relation.ReflTransGen.trans hyz hxy

@[simp] theorem containsOrEq_leaf {a : α} {y : SyntacticObject α} :
    ContainsOrEq (leaf a) y ↔ y = leaf a := by
  rw [← mem_terms_iff_containsOrEq, terms_leaf, Multiset.mem_singleton]

theorem containsOrEq_mul {l r y : SyntacticObject α} :
    ContainsOrEq (l * r) y ↔ y = l * r ∨ ContainsOrEq l y ∨ ContainsOrEq r y := by
  simp only [← mem_terms_iff_containsOrEq, terms_mul, Multiset.mem_cons, Multiset.mem_add]

theorem Contains.containsOrEq {x y : SyntacticObject α} (h : Contains x y) : ContainsOrEq x y :=
  Relation.TransGen.to_reflTransGen h

/-- The lexical items of an object. -/
def yield : SyntacticObject α → Multiset α :=
  FreeCommMagma.elim (fun a ↦ {a}) (fun _ _ a b ↦ a + b) fun _ _ a b ↦ add_comm a b

@[simp] theorem yield_leaf (a : α) : (leaf a).yield = {a} := rfl

@[simp] theorem yield_mul (l r : SyntacticObject α) : (l * r).yield = l.yield + r.yield :=
  FreeCommMagma.elim_mul _ _ _ l r

theorem card_yield_pos (x : SyntacticObject α) : 0 < x.yield.card := by
  induction x using FreeCommMagma.inductionOn with
  | of a => simp
  | mul l r ihl _ => rw [yield_mul, Multiset.card_add]; omega

theorem IsDaughter.card_yield_lt {x y : SyntacticObject α} (h : IsDaughter y x) :
    y.yield.card < x.yield.card := by
  obtain ⟨z, rfl⟩ := h
  rw [yield_mul, Multiset.card_add]
  have := card_yield_pos z
  omega

theorem Contains.card_yield_lt {x y : SyntacticObject α} (h : Contains x y) :
    y.yield.card < x.yield.card := by
  induction h with
  | single h => exact h.card_yield_lt
  | tail _ h ih => exact ih.trans h.card_yield_lt

/-- No object contains itself. -/
theorem not_contains_self (x : SyntacticObject α) : ¬ Contains x x := fun h ↦
  lt_irrefl _ h.card_yield_lt

theorem yield_le_of_mem_terms {x y : SyntacticObject α} (h : y ∈ x.terms) : y.yield ≤ x.yield := by
  induction x using FreeCommMagma.inductionOn with
  | of a =>
    rw [terms_leaf, Multiset.mem_singleton] at h
    rw [h]
  | mul l r ihl ihr =>
    rw [terms_mul, Multiset.mem_cons, Multiset.mem_add] at h
    rw [yield_mul]
    rcases h with rfl | h | h
    · rw [yield_mul]
    · exact (ihl h).trans (Multiset.le_add_right _ _)
    · exact (ihr h).trans (Multiset.le_add_left _ _)

theorem contains_iff_containsOrEq_and_ne {x y : SyntacticObject α} :
    Contains x y ↔ ContainsOrEq x y ∧ x ≠ y := by
  refine ⟨fun h ↦ ⟨h.containsOrEq, fun e ↦ not_contains_self x (e ▸ h)⟩, fun ⟨h, hne⟩ ↦ ?_⟩
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with h | h
  · exact absurd h hne
  · exact h

end SyntacticObject

/-! ### The tree of an object -/

namespace PlanarSyntacticObject

/-- Forgetting the order of daughters. -/
@[coe] def toSyntacticObject (p : PlanarSyntacticObject α) : SyntacticObject α :=
  FreeMagma.toFreeCommMagma p

instance : Coe (PlanarSyntacticObject α) (SyntacticObject α) := ⟨toSyntacticObject⟩

/-- Forgetting the order of daughters, as a morphism of magmas. -/
def toSyntacticObjectHom : PlanarSyntacticObject α →ₙ* SyntacticObject α :=
  FreeMagma.toFreeCommMagma

@[simp] theorem coe_toSyntacticObjectHom :
    ⇑(toSyntacticObjectHom : PlanarSyntacticObject α →ₙ* SyntacticObject α) = toSyntacticObject :=
  rfl

@[simp] theorem toSyntacticObject_of (a : α) :
    toSyntacticObject (FreeMagma.of a : PlanarSyntacticObject α) = SyntacticObject.leaf a := rfl

@[simp] theorem toSyntacticObject_mul (l r : PlanarSyntacticObject α) :
    toSyntacticObject (l * r) = toSyntacticObject l * toSyntacticObject r :=
  map_mul toSyntacticObjectHom l r

/-- The tree of a planar object: a leaf carries its item, a Merge carries nothing. -/
def toRoseTree : PlanarSyntacticObject α → RoseTree (Option α)
  | .of a => .node (some a) []
  | .mul l r => .node none [toRoseTree l, toRoseTree r]

/-- The lexical items of a planar object, in order. -/
def yield : PlanarSyntacticObject α → List α
  | .of a => [a]
  | .mul l r => yield l ++ yield r

theorem coe_yield (p : PlanarSyntacticObject α) :
    (p.yield : Multiset α) = (p : SyntacticObject α).yield := by
  induction p with
  | of a => rfl
  | mul l r ihl ihr =>
    show ((yield l ++ yield r : List α) : Multiset α) = _
    rw [← Multiset.coe_add, ihl, ihr]
    exact (FreeCommMagma.elim_mul _ _ _ _ _).symm

/-- The planar object at an address of a planar object. -/
def subAt? : PlanarSyntacticObject α → List ℕ → Option (PlanarSyntacticObject α)
  | p, [] => some p
  | .mul l _, 0 :: q => subAt? l q
  | .mul _ r, 1 :: q => subAt? r q
  | _, _ => none

/-- The subtree at an address is the tree of the planar object there. -/
theorem getElem?_toRoseTree (p : PlanarSyntacticObject α) (q : List ℕ) :
    p.toRoseTree[q]? = (p.subAt? q).map toRoseTree := by
  induction p generalizing q with
  | of a => cases q <;> simp [toRoseTree, subAt?]
  | mul l r ihl ihr =>
    rcases q with _ | ⟨_ | _ | n, q⟩
    · rfl
    · exact (ihl q).trans rfl
    · exact (ihr q).trans rfl
    · show (RoseTree.node none [toRoseTree l, toRoseTree r])[(n + 2) :: q]? = none
      simp

/-- The object at an address of a planar object. -/
def termAt? (p : PlanarSyntacticObject α) (q : List ℕ) : Option (SyntacticObject α) :=
  (p.subAt? q).map toSyntacticObject

theorem isSome_termAt? (p : PlanarSyntacticObject α) (q : p.toRoseTree.Positions) :
    (p.termAt? q.val.toList).isSome := by
  have h : (p.toRoseTree[q.val.toList]?).isSome := q.2
  rw [getElem?_toRoseTree] at h
  simpa [termAt?] using h

/-- The object at a position: the unfolding from occurrences to values. -/
def termAt (p : PlanarSyntacticObject α) (q : p.toRoseTree.Positions) : SyntacticObject α :=
  (p.termAt? q.val.toList).get (p.isSome_termAt? q)

/-- The terms of an object are the objects at the positions of any planar form of it. -/
theorem mem_terms_iff_exists_termAt? (p : PlanarSyntacticObject α) {y : SyntacticObject α} :
    y ∈ (p : SyntacticObject α).terms ↔ ∃ q, p.termAt? q = some y := by
  induction p with
  | of a =>
    show y ∈ ({SyntacticObject.leaf a} : Multiset _) ↔ _
    rw [Multiset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨[], rfl⟩
    · rintro ⟨_ | ⟨i, q⟩, h⟩
      · exact (Option.some.inj h).symm
      · simp [termAt?, subAt?] at h
  | mul l r ihl ihr =>
    show y ∈ ((l : SyntacticObject α) * (r : SyntacticObject α)).terms ↔ _
    rw [SyntacticObject.terms_mul, Multiset.mem_cons, Multiset.mem_add, ihl, ihr]
    constructor
    · rintro (rfl | ⟨q, h⟩ | ⟨q, h⟩)
      · exact ⟨[], rfl⟩
      · exact ⟨0 :: q, h⟩
      · exact ⟨1 :: q, h⟩
    · rintro ⟨_ | ⟨_ | _ | n, q⟩, h⟩
      · exact .inl (Option.some.inj h).symm
      · exact .inr (.inl ⟨q, h⟩)
      · exact .inr (.inr ⟨q, h⟩)
      · have h' : (none : Option (SyntacticObject α)) = some y := h
        cases h'

theorem mem_terms_iff_exists_termAt (p : PlanarSyntacticObject α) {y : SyntacticObject α} :
    y ∈ (p : SyntacticObject α).terms ↔ ∃ q, p.termAt q = y := by
  rw [mem_terms_iff_exists_termAt?]
  constructor
  · rintro ⟨q, h⟩
    have hq : (p.toRoseTree[q]?).isSome := by
      rw [getElem?_toRoseTree]
      have h' : (p.termAt? q).isSome := by rw [h]; rfl
      simpa [termAt?] using h'
    exact ⟨⟨⟨q⟩, hq⟩, by simp [termAt, h]⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.val.toList, by simp [termAt]⟩

/-- Copies: two positions hold one element when they hold the same object. -/
def chain (p : PlanarSyntacticObject α) : Setoid p.toRoseTree.Positions := Setoid.ker p.termAt

end PlanarSyntacticObject

namespace SyntacticObject

/-- The tree of an object, with no order on daughters. -/
def toUnorderedTree : SyntacticObject α → UnorderedTree (Option α) :=
  FreeCommMagma.elim (fun a ↦ .leaf (some a)) (fun _ _ a b ↦ .node none {a, b})
    fun _ _ a b ↦ by rw [Multiset.pair_comm]

theorem toUnorderedTree_coe (p : PlanarSyntacticObject α) :
    (p : SyntacticObject α).toUnorderedTree = .mk p.toRoseTree := by
  induction p with
  | of a => rfl
  | mul l r ihl ihr =>
    show toUnorderedTree ((l : SyntacticObject α) * (r : SyntacticObject α)) = _
    rw [toUnorderedTree, FreeCommMagma.elim_mul, ← toUnorderedTree, ihl, ihr]
    exact UnorderedTree.node_pair_mk none _ _

@[simp] theorem toUnorderedTree_leaf (a : α) :
    (leaf a).toUnorderedTree = UnorderedTree.leaf (some a) := rfl

@[simp] theorem toUnorderedTree_mul (l r : SyntacticObject α) :
    (l * r).toUnorderedTree = .node none {l.toUnorderedTree, r.toUnorderedTree} :=
  FreeCommMagma.elim_mul _ _ _ l r

theorem IsDaughter.numNodes_lt {x y : SyntacticObject α} (h : IsDaughter y x) :
    y.toUnorderedTree.numNodes < x.toUnorderedTree.numNodes := by
  obtain ⟨z, rfl⟩ := h
  rw [toUnorderedTree_mul, UnorderedTree.numNodes_node]
  simp
  omega

/-- A proper term of an object has fewer nodes. -/
theorem numNodes_lt_of_contains {x y : SyntacticObject α} (h : Contains x y) :
    y.toUnorderedTree.numNodes < x.toUnorderedTree.numNodes := by
  induction h with
  | single h => exact h.numNodes_lt
  | tail _ h ih => exact ih.trans h.numNodes_lt

end SyntacticObject

/-! ### Relabelling the lexical items -/

/-- A map of lexical items relabels the leaves. -/
abbrev SyntacticObject.map (f : α → β) : SyntacticObject α →ₙ* SyntacticObject β :=
  FreeCommMagma.map f

theorem SyntacticObject.terms_map (f : α → β) (x : SyntacticObject α) :
    (SyntacticObject.map f x).terms = x.terms.map (SyntacticObject.map f) := by
  induction x using FreeCommMagma.inductionOn with
  | of a => rfl
  | mul l r ihl ihr =>
    rw [map_mul, SyntacticObject.terms_mul, SyntacticObject.terms_mul, ihl, ihr,
      Multiset.map_cons, Multiset.map_add, map_mul]

end Minimalist.Next
