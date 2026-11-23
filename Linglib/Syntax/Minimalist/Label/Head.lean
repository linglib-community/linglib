/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Linglib.Syntax.Minimalist.LexicalItem

/-!
# Head functions

A licensing of Merge is a morphism of magmas out of the syntactic objects into a commutative magma
with zero, `0` being the failure of Merge, and its head function reads a head off each value.
Marcolli, Chomsky and Berwick's head functions are partial, and the head of a Merge is the head of
the daughter that projects. A function `head` on the target is a head function when `0` has no
head and the head of a product is the head of one of its factors, so the head function of every
licensing is endocentric. Where `0` absorbs, the domain of a licensing is closed under daughters
(`ne_zero_and_ne_zero_of_mul` after `map_mul`), though not under Merge, since an exocentric Merge of
two headed objects has no head. The heads of selection states, copy states and raising states are
head functions.

## Main definitions

* `Minimalist.IsHeadFunction`: a head function on a magma with zero.

## Main statements

* `Minimalist.IsHeadFunction.comp`: the head of the image of a product under a morphism of magmas
  is the head of the image of a factor.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

variable {β : Type*} [Mul β] [Zero β] {head : β → Option LexicalItem.Token}

/-- A head function on a magma with zero: `0`, the failure of Merge, has no head, and the head of
a product is the head of one of its factors, the characterization of heads in
[marcolli-chomsky-berwick-2025], Lemma 1.13.7. -/
structure IsHeadFunction (head : β → Option LexicalItem.Token) : Prop where
  /-- The failure of Merge has no head. -/
  map_zero : head 0 = none
  /-- The head of a product is the head of a factor. -/
  mem_or_mem_of_mem_mul : ∀ {x y : β} {t : LexicalItem.Token},
    t ∈ head (x * y) → t ∈ head x ∨ t ∈ head y

/-- The head of the image of a product is the head of a factor's image: a licensing's head
function is endocentric ([marcolli-chomsky-berwick-2025], Lemma 1.13.7). -/
theorem IsHeadFunction.comp (h : IsHeadFunction head) {M : Type*} [Mul M] (φ : M →ₙ* β) {x y : M}
    {t : LexicalItem.Token} (ht : t ∈ head (φ (x * y))) : t ∈ head (φ x) ∨ t ∈ head (φ y) :=
  h.mem_or_mem_of_mem_mul (map_mul φ x y ▸ ht)

end Minimalist
