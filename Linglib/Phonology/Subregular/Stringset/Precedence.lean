module

public import Linglib.Phonology.Subregular.Stringset.StrictlyPiecewise
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.RelIso.Basic

/-!
# Languages of a precedence relation

For a relation `R` on an alphabet, `Language.pairwise R` is the set of strings in which every
letter stands in `R` to every later letter: `R a b` reads "`a` may stand somewhere before `b`".
These are the strictly 2-piecewise languages that contain every one-letter string.

For two letters `a` and `b`, the relation leaves three cases: the order is fixed when exactly
one of `R a b` and `R b a` holds, free when both hold, and `a` and `b` exclude each other when
neither does.

The map `R ↦ Language.pairwise R` is an order embedding of relations into languages,
`Language.pairwiseOrderEmbedding`, and commutes with inverse images of letter-to-letter maps,
`Language.preimage_map_pairwise`.

## References

* [rogers-heinz-et-al-2010]
-/

@[expose] public section

namespace Language

open List

variable {α β : Type*} {R S : α → α → Prop} {a b : α} {w : List α}

/-- The language of the precedence relation `R`: the strings in which every letter stands in
`R` to every later letter. -/
def pairwise (R : α → α → Prop) : Language α := {w | w.Pairwise R}

@[simp] theorem mem_pairwise : w ∈ pairwise R ↔ w.Pairwise R := .rfl

instance [DecidableRel R] : DecidablePred (· ∈ pairwise R) :=
  fun w ↦ inferInstanceAs (Decidable (w.Pairwise R))

theorem pair_mem_pairwise : [a, b] ∈ pairwise R ↔ R a b := by simp

theorem isSublistClosed_pairwise : (pairwise R).IsSublistClosed :=
  fun _ _ hvw hw ↦ hw.sublist hvw

theorem isStrictlyPiecewise_pairwise : (pairwise R).IsStrictlyPiecewise 2 := by
  refine ⟨pairwise R, Set.ext fun w ↦ ⟨fun h ↦ ?_, fun h s _ hs ↦ isSublistClosed_pairwise hs h⟩⟩
  exact pairwise_iff_forall_sublist.2 fun hab ↦ pair_mem_pairwise.1 (h _ (by simp) hab)

theorem pairwise_le_pairwise_iff : pairwise R ≤ pairwise S ↔ R ≤ S :=
  ⟨fun h _ _ hab ↦ pair_mem_pairwise.1 (h (pair_mem_pairwise.2 hab)),
    fun h _ hw ↦ hw.imp (h _ _)⟩

/-- A relation is recovered from its language, and a weaker relation has the larger language. -/
def pairwiseOrderEmbedding : (α → α → Prop) ↪o Language α :=
  OrderEmbedding.ofMapLEIff pairwise fun _ _ ↦ pairwise_le_pairwise_iff

@[simp] theorem coe_pairwiseOrderEmbedding :
    ⇑(pairwiseOrderEmbedding (α := α)) = pairwise := rfl

theorem pairwise_inf : pairwise (R ⊓ S) = pairwise R ⊓ pairwise S :=
  Set.ext fun _ ↦ List.pairwise_and_iff

/-- The strings whose images under `f` are in the language of `R` are the language of the
relation pulled back along `f`. -/
theorem preimage_map_pairwise (f : β → α) :
    List.map f ⁻¹' pairwise R = pairwise (f ⁻¹'o R) :=
  Set.ext fun _ ↦ List.pairwise_map

end Language
