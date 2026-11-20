module

public import Linglib.Semantics.Mereology.Classical
public import Mathlib.Data.Fintype.Powerset

/-!
# Cotnoir and Varzi (2021): Mereology

Classical mereology is a partial order with a least upper bound for every nonempty set and
Remainder: if `x` is not part of `y`, something has as parts exactly the parts of `x` that do
not overlap `y`. The decomposition principles weaker than Remainder come apart on small models.

In the model `Diamond`, three individuals `b₁`, `b₂`, `b₃` with no common part lie below a
fourth, `a`, and any two of them sum to `a`. A proper part of `a` has a remainder that sums with
it to `a`, so Additive Remainder holds (`Diamond.additiveRemainder`), and Strong Supplementation
holds, but the remainder is not unique and Remainder fails (`Diamond.not_remainder`): nothing has
as parts exactly the parts of `a` that do not overlap `b₁`.

In the model `Butterfly`, two individuals `c` and `d` lie below each of two others, `a` and
`b`. Weak Supplementation holds and Strong Supplementation fails
(`Butterfly.not_strongSupplementation`): `a` is not part of `b`, and every part of `a` overlaps
`b`. In the model `Tent`, Strong Supplementation holds and Remainder fails
(`Tent.not_remainder`). A two-element chain satisfies neither supplementation principle.

The nonempty subsets of a three-element set are a classical mereology
(`isClassical_nonempty_subsets`).

## Implementation notes

The models are the book's figures: the two-element chain and `Butterfly` are its two failures
of Remainder, `Diamond` its model of Additive Remainder without remainders, `Tent` its model of
Strong Supplementation with missing remainders, and the nonempty subsets of a three-element set
its three-atom Boolean algebra without the empty set. The orders are given by their graphs, and
the statements are decided by enumeration. Weak Supplementation is stated with a part that does
not overlap the proper part, which in a partial order is a proper part.

## References

* [cotnoir-varzi-2021]
* [cotnoir-varzi-2019]
-/

@[expose] public section

namespace CotnoirVarzi2021

open Mereology

/-! ### Additive Remainder without Remainder -/

/-- Three individuals with no common part below a fourth. -/
inductive Diamond
  | b₁ | b₂ | b₃ | a
  deriving DecidableEq

namespace Diamond

instance : Fintype Diamond := ⟨{b₁, b₂, b₃, a}, fun x ↦ by cases x <;> simp⟩

instance : PartialOrder Diamond where
  le x y := x = y ∨ y = a
  le_refl _ := .inl rfl
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Diamond := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

instance : DecidableLT Diamond := decidableLTOfDecidableLE

instance : SemilatticeSup Diamond where
  sup x y := if x = y then x else a
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide

/-- Additive Remainder holds: a proper part has something that does not overlap it and sums
with it to the whole. -/
theorem additiveRemainder : AdditiveRemainder Diamond := by
  unfold AdditiveRemainder Overlap
  decide

theorem strongSupplementation : StrongSupplementation Diamond := by
  unfold StrongSupplementation Overlap
  decide

-- `b₂` and `b₃` are both remainders of `b₁` in `a`.
theorem not_uniqueAdditiveRemainder : ¬ UniqueAdditiveRemainder Diamond := fun h ↦
  absurd ((h (x := b₁) (y := a) (by decide)).unique (y₁ := b₂) (y₂ := b₃)
    (by unfold Overlap; decide) (by unfold Overlap; decide)) (by decide)

/-- Remainder fails: nothing has as parts exactly the parts of `a` that do not overlap `b₁`. -/
theorem not_remainder : ¬ Remainder Diamond := by
  unfold Remainder Overlap
  decide

end Diamond

/-! ### Weak without Strong Supplementation -/

/-- Two individuals below each of two others. -/
inductive Butterfly
  | c | d | a | b
  deriving DecidableEq

namespace Butterfly

instance : Fintype Butterfly := ⟨{c, d, a, b}, fun x ↦ by cases x <;> simp⟩

instance : PartialOrder Butterfly where
  le x y := x = y ∨ ((x = c ∨ x = d) ∧ (y = a ∨ y = b))
  le_refl _ := .inl rfl
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Butterfly := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

instance : DecidableLT Butterfly := decidableLTOfDecidableLE

theorem weakSupplementation : WeakSupplementation Butterfly := by
  unfold WeakSupplementation Overlap
  decide

-- `a` and `b` overlap the same things and are distinct, so overlap does not determine identity.
theorem exists_ne_forall_overlap_iff :
    ∃ x y : Butterfly, x ≠ y ∧ ∀ z, Overlap z x ↔ Overlap z y := by
  unfold Overlap
  decide

/-- Strong Supplementation fails: `a` is not part of `b`, and every part of `a` overlaps
`b`. -/
theorem not_strongSupplementation : ¬ StrongSupplementation Butterfly := by
  unfold StrongSupplementation Overlap
  decide

end Butterfly

/-! ### Strong Supplementation without Remainder -/

/-- An individual `b` below two others, each of which has a further part, all below `a`. -/
inductive Tent
  | c₁ | b | c₂ | m₁ | m₂ | a
  deriving DecidableEq

namespace Tent

instance : Fintype Tent := ⟨{c₁, b, c₂, m₁, m₂, a}, fun x ↦ by cases x <;> simp⟩

instance : PartialOrder Tent where
  le x y := x = y ∨ y = a ∨ (y = m₁ ∧ (x = c₁ ∨ x = b)) ∨ (y = m₂ ∧ (x = b ∨ x = c₂))
  le_refl _ := .inl rfl
  le_trans := by decide
  le_antisymm := by decide

instance : DecidableLE Tent := fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))

theorem strongSupplementation : StrongSupplementation Tent := by
  unfold StrongSupplementation Overlap
  decide

/-- Remainder fails: `b` has two supplements in `a`, and nothing has exactly them as parts. -/
theorem not_remainder : ¬ Remainder Tent := by
  unfold Remainder Overlap
  decide

end Tent

/-! ### A two-element chain -/

-- A whole with a single proper part has no supplement of it.
theorem not_weakSupplementation_bool : ¬ WeakSupplementation Bool := by
  unfold WeakSupplementation Overlap
  decide

theorem not_remainder_bool : ¬ Remainder Bool := by
  unfold Remainder Overlap
  decide

/-! ### A classical mereology -/

/-- The nonempty subsets of a three-element set are a classical mereology, with no least
element. -/
theorem isClassical_nonempty_subsets :
    IsClassical {s : Set (Fin 3) // s ≠ ⊥} ∧ ¬ ∃ z : {s : Set (Fin 3) // s ≠ ⊥}, ∀ y, z ≤ y :=
  ⟨isClassical_subtype_ne_bot, isClassical_subtype_ne_bot.remainder.no_zero
    (a := ⟨{0}, Set.singleton_ne_empty 0⟩) (b := ⟨{1}, Set.singleton_ne_empty 1⟩)
    fun h ↦ by simpa using congrArg Subtype.val h⟩

end CotnoirVarzi2021
