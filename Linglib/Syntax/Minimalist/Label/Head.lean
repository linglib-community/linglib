/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Head functions

A head function gives the item that heads a syntactic object, where the object has a head.
Following [marcolli-chomsky-berwick-2025], a function `h` from syntactic objects to items is a head
function when an item is the only head its own leaf can have and the head of a Merge is the head
of one of the two objects merged. An object then contains the leaf of its head.

## Main definitions

* `Minimalist.IsHeadFunction`: a head function on syntactic objects.

## Main results

* `Minimalist.IsHeadFunction.leaf_mem_terms`: an object contains the leaf of its head.

## Implementation notes

* A head function is partial, with values in `Option`: the Merge of two objects neither of which
  projects is exocentric and has no head, and an item that does not label has none either.
* A head function here is a function of the object. The head daughter at each position of a planar
  object, which may depend on the object the position lies in, is `Minimalist.HeadDaughter` of
  `SyntacticObject/Projection.lean`.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

variable {α : Type} {h : SyntacticObject α → Option α} {s : SyntacticObject α} {a : α}

/-- A head function on syntactic objects: an item is the only head of its leaf, and the head of a
Merge is the head of a daughter, the characterization of heads in
[marcolli-chomsky-berwick-2025], Lemma 1.13.7. -/
structure IsHeadFunction (h : SyntacticObject α → Option α) : Prop where
  /-- An item is the only head its leaf can have. -/
  eq_of_mem_leaf : ∀ {a b : α}, b ∈ h (leaf a) → b = a
  /-- The head of a Merge is the head of a daughter. -/
  mem_or_mem : ∀ {x y : SyntacticObject α} {a : α}, a ∈ h (x * y) → a ∈ h x ∨ a ∈ h y

namespace IsHeadFunction

/-- An object contains the leaf of its head. -/
theorem leaf_mem_terms (hh : IsHeadFunction h) (hs : a ∈ h s) : leaf a ∈ s.terms := by
  induction s using FreeCommMagma.inductionOn with
  | of b =>
    obtain rfl := hh.eq_of_mem_leaf hs
    exact SyntacticObject.mem_terms.2 .refl
  | mul l r ihl ihr =>
    rw [terms_mul]
    rcases hh.mem_or_mem hs with h' | h'
    · exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inl (ihl h')))
    · exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inr (ihr h')))

end IsHeadFunction

end Minimalist
