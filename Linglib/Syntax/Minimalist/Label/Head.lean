/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Head functions

A head function gives the lexical item that heads a syntactic object, where the object has a
head. Following [marcolli-chomsky-berwick-2025], a function `h` from syntactic objects to lexical
items is a head function when a lexical item is the only head its own leaf can have and the head
of a Merge is the head of one of the two objects merged. The head of an object is then the head of
one of its leaves, and an object headed by a lexical item that heads none of its traces contains
the leaf of that item.

## Main definitions

* `Minimalist.IsHeadFunction`: a head function on syntactic objects.

## Main results

* `Minimalist.IsHeadFunction.exists_mem_terms`: the head of an object is the head of a leaf of it.
* `Minimalist.IsHeadFunction.leaf_mem_terms`: an object contains the leaf of its head.

## Implementation notes

* A head function is partial, with values in `Option`: the Merge of two objects neither of which
  projects is exocentric and has no head, and a lexical item that does not label has none either.
* The head is a lexical item and a trace is a leaf that is not one, so a head function may give a
  trace a head: the selection head of a labelled trace is the item it is the trace of. What is
  proved about the leaf of a head therefore assumes that the head heads no trace of the object.
* A head function here is a function of the object. The head daughter at each position of a planar
  object, which may depend on the object the position lies in, is `Minimalist.HeadDaughter` of
  `SyntacticObject/Projection.lean`.

## References

* [marcolli-chomsky-berwick-2025]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

variable {L ι : Type} {h : SyntacticObject (SyntacticObject.Leaf L ι) → Option L}
    {s : SyntacticObject (SyntacticObject.Leaf L ι)} {a ℓ : L}

/-- A head function on syntactic objects: a lexical item is the only head of its leaf, and the
head of a Merge is the head of a daughter, the characterization of heads in
[marcolli-chomsky-berwick-2025], Lemma 1.13.7. -/
structure IsHeadFunction (h : SyntacticObject (SyntacticObject.Leaf L ι) → Option L) : Prop where
  /-- A lexical item is the only head its leaf can have. -/
  eq_of_mem_leaf : ∀ {a b : L}, b ∈ h (leaf a) → b = a
  /-- The head of a Merge is the head of a daughter. -/
  mem_or_mem : ∀ {x y : SyntacticObject (SyntacticObject.Leaf L ι)} {a : L}, a ∈ h (merge x y) → a
      ∈ h x ∨ a ∈ h y

namespace IsHeadFunction

/-- The head of an object is the head of one of its leaves. -/
theorem exists_mem_terms (hh : IsHeadFunction h) (ha : a ∈ h s) :
    ∃ l : Leaf L ι, FreeCommMagma.of l ∈ s.terms ∧ a ∈ h (FreeCommMagma.of l) := by
  induction s using SyntacticObject.ind with
  | leaf b => exact ⟨.lex b, SyntacticObject.mem_terms.2 .refl, ha⟩
  | trace => exact ⟨.trace, SyntacticObject.mem_terms.2 .refl, ha⟩
  | traceOf i => exact ⟨.traceOf i, SyntacticObject.mem_terms.2 .refl, ha⟩
  | merge l r ihl ihr =>
    rw [terms_merge]
    rcases hh.mem_or_mem ha with h' | h'
    · obtain ⟨x, hx, hxa⟩ := ihl h'
      exact ⟨x, Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inl hx)), hxa⟩
    · obtain ⟨x, hx, hxa⟩ := ihr h'
      exact ⟨x, Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inr hx)), hxa⟩

/-- An object headed by `ℓ`, no trace of which `ℓ` heads, contains the leaf of `ℓ`. -/
theorem leaf_mem_terms (hh : IsHeadFunction h) (htr : ∀ x ∈ s.terms, x.IsTrace → h x ≠ some ℓ)
    (hs : h s = some ℓ) : leaf ℓ ∈ s.terms := by
  obtain ⟨l, hl, hla⟩ := hh.exists_mem_terms (Option.mem_def.2 hs)
  rcases l with b | _ | i
  · obtain rfl := hh.eq_of_mem_leaf hla
    exact hl
  · exact absurd hla (htr _ hl (.inl rfl))
  · exact absurd hla (htr _ hl (.inr ⟨i, rfl⟩))

end IsHeadFunction

end Minimalist
