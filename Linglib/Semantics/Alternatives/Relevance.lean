module

public import Mathlib.Order.BooleanSubalgebra
public import Linglib.Semantics.Exhaustification.Excluder

/-!
# Relevance of alternatives

Fox and Katzir restrict the formal alternatives of a sentence to the contextually relevant ones,
with relevance closed under the Boolean operations. A sentence is exhaustively relevant given a
restriction when its *only*-meaning lies in the Boolean closure of the restriction, and a
restriction is allowable when it keeps the assertion and prunes nothing exhaustively relevant. A
set in the Boolean closure of a family does not separate worlds that every member of the family
treats alike (`mem_iff_of_mem_closure`), so an alternative whose *only*-meaning separates two such
worlds is not exhaustively relevant (`not_exhaustivelyRelevant_of_separates`). Relevance relative
to a context set is the same notion over the subtype of the context, each proposition restricted
to it by preimage.

## Main definitions

* `Alternatives.ExhaustivelyRelevant`, `Alternatives.IsAllowableRestriction`

## References

* [fox-katzir-2011]
-/

@[expose] public section

namespace Alternatives

open Exhaustification

variable {W : Type*}

/-- A sentence is exhaustively relevant given a restriction when its *only*-meaning lies in the
Boolean closure of the restriction. -/
def ExhaustivelyRelevant (A : Set (Set W)) (p : Set W) : Prop :=
  exh A p ∈ BooleanSubalgebra.closure A

/-- A restriction of the formal alternatives is allowable when it keeps the assertion and prunes
nothing exhaustively relevant. -/
def IsAllowableRestriction (F A : Set (Set W)) (S : Set W) : Prop :=
  S ∈ A ∧ ∀ p ∈ F \ A, ¬ ExhaustivelyRelevant A p

variable {A : Set (Set W)} {X p : Set W} {u v : W}

/-- A set in the Boolean closure of `A` does not separate worlds that every member of `A` treats
alike. -/
theorem mem_iff_of_mem_closure (hX : X ∈ BooleanSubalgebra.closure A)
    (h : ∀ a ∈ A, u ∈ a ↔ v ∈ a) : u ∈ X ↔ v ∈ X := by
  induction hX using BooleanSubalgebra.closure_bot_sup_induction with
  | mem a ha => exact h a ha
  | bot => exact Iff.rfl
  | sup x _ y _ hx hy => exact or_congr hx hy
  | compl x _ hx => exact not_congr hx

theorem not_exhaustivelyRelevant_of_separates (h : ∀ a ∈ A, u ∈ a ↔ v ∈ a)
    (hu : u ∈ exh A p) (hv : v ∉ exh A p) : ¬ ExhaustivelyRelevant A p :=
  fun hp ↦ hv ((mem_iff_of_mem_closure hp h).1 hu)

end Alternatives
