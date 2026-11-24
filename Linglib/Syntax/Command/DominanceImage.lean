/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Command.Basic
public import Linglib.Core.Relation.SetRel
public import Mathlib.Order.UpperLower.Closure

/-!
# Dominance images

A relation between the nodes of a dominance order induces one between the nodes they dominate,
its dominance image, relating `a` to `b` when a node dominating `a` is related to a node
dominating `b`: the upper closure of the relation in the product order, transported by order
isomorphisms. Kayne's linear
correspondence reads the dominance image of asymmetric c-command as precedence among terminals,
and on a tree two sisters that relate both ways
[stay unordered](##PhraseStructure.not_mem_dominanceImage_asymmetrize_of_covBy).

## References

* [kayne-1994]
-/

@[expose] public section

namespace PhraseStructure

open Order Set
open scoped SetRel

variable {α : Type*}

section DominanceImage

variable [Preorder α] {A : SetRel α α} {a b : α}

/-- The dominance image of a relation, relating the nodes dominated by related nodes. -/
abbrev dominanceImage (A : SetRel α α) : SetRel α α := upperClosure A

theorem mem_dominanceImage : a ~[dominanceImage A] b ↔ ∃ x ≤ a, ∃ y ≤ b, x ~[A] y := by
  simp only [SetLike.mem_coe, mem_upperClosure, Prod.exists, Prod.mk_le_mk]
  exact ⟨fun ⟨x, y, h, hx, hy⟩ ↦ ⟨x, hx, y, hy, h⟩, fun ⟨x, hx, y, hy, h⟩ ↦ ⟨x, y, h, hx, hy⟩⟩

/-- An order isomorphism carries the dominance image of a relation to that of its image, by
`upperClosure_image`. -/
theorem mem_dominanceImage_image {β : Type*} [Preorder β] (e : α ≃o β) :
    e a ~[dominanceImage (Prod.map e e '' A)] e b ↔ a ~[dominanceImage A] b := by
  rw [dominanceImage, show Prod.map e e = e.prodCongr e from rfl, upperClosure_image]
  exact (UpperSet.mem_map (f := e.prodCongr e) (b := (e a, e b))).trans (by simp)

end DominanceImage

section DominanceImageTree

variable [PartialOrder α] [IsForestOrder α] {R : SetRel α α} {a b m : α}

/-- Two daughters of one node are not related by the dominance image of the asymmetric part of a
relation between disconnected nodes that relates them both ways. -/
theorem not_mem_dominanceImage_asymmetrize_of_covBy
    (hR : ∀ ⦃x y⦄, x ~[R] y → IncompRel (· ≤ ·) x y) (hab : a ~[R] b → b ~[R] a)
    (ha : m ⋖ a) (hb : m ⋖ b) : ¬ a ~[dominanceImage R.asymmetrize] b := by
  rw [mem_dominanceImage]
  rintro ⟨x, hxa, y, hyb, hxy, hyx⟩
  obtain ⟨hn₁, hn₂⟩ := hR hxy
  rcases hxa.eq_or_lt with rfl | hx <;> rcases hyb.eq_or_lt with rfl | hy
  · exact hyx (hab hxy)
  · exact hn₂ ((IsForestOrder.le_of_lt_of_covBy hb hy).trans ha.le)
  · exact hn₁ ((IsForestOrder.le_of_lt_of_covBy ha hx).trans hb.le)
  · exact (IsForestOrder.le_total_of_le_of_le (IsForestOrder.le_of_lt_of_covBy ha hx)
      (IsForestOrder.le_of_lt_of_covBy hb hy)).elim hn₁ hn₂

end DominanceImageTree

end PhraseStructure
