/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Linglib.Syntax.Minimalist.LexicalItem

/-!
# Heads

A licensing of Merge is a morphism of magmas out of the syntactic objects into a commutative magma
with zero, `0` being the failure of Merge, and its head function reads a head off each value.
Marcolli, Chomsky and Berwick's head functions are partial, and the head of a Merge is the head of
the daughter that projects; `Head` records that law on the target, so the head function of every
licensing is endocentric. Where `0` absorbs, the domain of a licensing is closed under daughters
(`ne_zero_and_ne_zero_of_mul` after `map_mul`), though not under Merge, since an exocentric Merge of
two headed objects has no head. Selection, copy states and raising are instances.

## Main definitions

* `Minimalist.Head`: an endocentric head on a magma with zero.

## Main statements

* `Minimalist.mem_head_or_mem_head_of_mem_head_mul`: a product's head is a factor's head.
* `Minimalist.mem_head_or_mem_head_of_mem_head_map_mul`: so is the head of the image of a
  product under a morphism of magmas.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

/-- An endocentric head on a magma with zero: `0`, the failure of Merge, has no head, and the head
of a product is the head of one of its factors, the characterization of heads in
[marcolli-chomsky-berwick-2025], Lemma 1.13.7. -/
class Head (β : Type*) [Mul β] [Zero β] where
  /-- The projecting head, if any. -/
  head : β → Option LexicalItem.Token
  protected head_zero : head 0 = none
  protected mem_head_or_mem_head_of_mem_head_mul {x y : β} {t : LexicalItem.Token} :
    t ∈ head (x * y) → t ∈ head x ∨ t ∈ head y

export Head (head)

variable {β : Type*} [Mul β] [Zero β] [Head β]

@[simp] theorem head_zero : head (0 : β) = none := Head.head_zero

theorem mem_head_or_mem_head_of_mem_head_mul {x y : β} {t : LexicalItem.Token}
    (h : t ∈ head (x * y)) : t ∈ head x ∨ t ∈ head y :=
  Head.mem_head_or_mem_head_of_mem_head_mul h

/-- The head of the image of a product is the head of a factor's image: a licensing's head
function is endocentric ([marcolli-chomsky-berwick-2025], Lemma 1.13.7). -/
theorem mem_head_or_mem_head_of_mem_head_map_mul {M : Type*} [Mul M] (φ : M →ₙ* β) {x y : M}
    {t : LexicalItem.Token} (h : t ∈ head (φ (x * y))) : t ∈ head (φ x) ∨ t ∈ head (φ y) :=
  mem_head_or_mem_head_of_mem_head_mul (map_mul φ x y ▸ h)

end Minimalist
