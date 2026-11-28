/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Hom.Lattice
public import Mathlib.Order.Nat
public import Mathlib.Order.SupClosed
public import Mathlib.Order.UpperLower.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Strengths of negation

This file defines the strengths of negation a context can carry, Zwarts's hierarchy of weak,
anti-additive and antimorphic contexts, which are van der Wouden's minimal, regular and classical
negation. A map between Boolean algebras is *monotone decreasing* if it reverses the order,
*anti-additive* if `f (x ⊔ y) = f x ⊓ f y`, and *antimorphic* if it is anti-additive and
`f xᶜ = (f x)ᶜ`, as clausal negation is. Each class contains the next, and the order on the three
strengths is that inclusion. A truth-valued map is monotone decreasing when the elements it holds
of form a lower set, and anti-additive when that lower set is also closed under joins.

## Main definitions

* `Negation.Strength`: the three strengths, a chain.
* `Negation.Strength.HoldsFor`: a map has a strength.

## Main results

* `Negation.Strength.HoldsFor.of_le`: a map of a strength has every weaker strength.
* `Negation.Strength.le_iff_forall_holdsFor`: one strength is below another exactly when every map
  of the second has the first.
* `Negation.Strength.holdsFor_antiAdditive_iff`: a truth-valued map is anti-additive exactly when
  the elements it holds of form a lower set closed under joins.

## Implementation notes

The conditions are written on mathlib's order, with no named predicate between: the classes are
those of the maps `x ↦ OrderDual.toDual (f x)` that are monotone, that preserve joins, and that
also commute with complement.

## References

* [zwarts-1998]
* [vanderwouden-1997]
* [ladusaw-1979]
-/

@[expose] public section

namespace Negation

/-- The three strengths of negation, `weak` plain downward entailment, `antiAdditive` adding the
∨→∧ distributivity of *nobody*, and `antiMorphic` the ∧→∨ distributivity of clausal negation. -/
inductive Strength where
  | weak
  | antiAdditive
  | antiMorphic
  deriving DecidableEq, Repr, Fintype

namespace Strength

/-- Rank in the chain `weak < antiAdditive < antiMorphic`. -/
def toNat : Strength → ℕ
  | .weak => 0
  | .antiAdditive => 1
  | .antiMorphic => 2

theorem toNat_injective : Function.Injective toNat := by decide

/-- The Zwarts hierarchy as the linear order `weak < antiAdditive < antiMorphic`. -/
instance : LinearOrder Strength :=
  LinearOrder.lift' toNat toNat_injective

instance : BoundedOrder Strength where
  bot := weak
  bot_le := by decide
  top := antiMorphic
  le_top := by decide

@[simp] theorem bot_eq_weak : (⊥ : Strength) = weak := rfl

@[simp] theorem top_eq_antiMorphic : (⊤ : Strength) = antiMorphic := rfl

@[simp] theorem weak_le (s : Strength) : weak ≤ s := bot_le

@[simp] theorem le_antiMorphic (s : Strength) : s ≤ antiMorphic := le_top

@[simp] theorem le_weak_iff {s : Strength} : s ≤ weak ↔ s = weak := le_bot_iff

/-! ### The maps of a strength -/

section HoldsFor

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β] {s t : Strength} {f : α → β}

/-- A map has a strength of negation: it is monotone decreasing, anti-additive, or antimorphic
([zwarts-1998]'s (91), (107) and (114)). -/
def HoldsFor : Strength → (α → β) → Prop
  | weak, f => Antitone f
  | antiAdditive, f => ∀ x y, f (x ⊔ y) = f x ⊓ f y
  | antiMorphic, f => (∀ x y, f (x ⊔ y) = f x ⊓ f y) ∧ ∀ x, f xᶜ = (f x)ᶜ

@[simp] theorem holdsFor_weak : weak.HoldsFor f ↔ Antitone f := Iff.rfl

@[simp] theorem holdsFor_antiAdditive : antiAdditive.HoldsFor f ↔ ∀ x y, f (x ⊔ y) = f x ⊓ f y :=
  Iff.rfl

@[simp] theorem holdsFor_antiMorphic :
    antiMorphic.HoldsFor f ↔ (∀ x y, f (x ⊔ y) = f x ⊓ f y) ∧ ∀ x, f xᶜ = (f x)ᶜ :=
  Iff.rfl

private theorem antitone_of_map_sup (h : ∀ x y, f (x ⊔ y) = f x ⊓ f y) : Antitone f :=
  Monotone.of_map_sup (β := βᵒᵈ) h

/-- A map of a strength has every weaker strength. -/
theorem HoldsFor.of_le (h : t.HoldsFor f) (hst : s ≤ t) : s.HoldsFor f := by
  cases s <;> cases t
  · exact h
  · exact antitone_of_map_sup h
  · exact antitone_of_map_sup h.1
  · exact absurd hst (by decide)
  · exact h
  · exact h.1
  · exact absurd hst (by decide)
  · exact absurd hst (by decide)
  · exact h

/-- One strength is below another exactly when every map of the second has the first. -/
theorem le_iff_forall_holdsFor :
    s ≤ t ↔ ∀ f : Set Bool → Prop, t.HoldsFor f → s.HoldsFor f := by
  refine ⟨fun h f hf ↦ hf.of_le h, fun h ↦ ?_⟩
  have hT : ({true} : Set Bool) ≠ Set.univ := fun h ↦ by simpa using Set.ext_iff.1 h false
  have hF : ({false} : Set Bool) ≠ Set.univ := fun h ↦ by simpa using Set.ext_iff.1 h true
  -- `(· ≠ univ)` is monotone decreasing and not anti-additive
  have a1 : Antitone fun S : Set Bool ↦ S ≠ Set.univ := fun A B hAB hB hA ↦
    hB (Set.univ_subset_iff.1 (hA ▸ hAB))
  have h1 : ¬∀ S T : Set Bool, (S ∪ T ≠ Set.univ) = (S ≠ Set.univ ∧ T ≠ Set.univ) := fun ha ↦
    (eq_iff_iff.1 (ha {true} {false})).2 ⟨hT, hF⟩ (by ext b; cases b <;> simp)
  -- `(· = ∅)` is anti-additive and does not commute with complement
  have a2 : ∀ S T : Set Bool, (S ∪ T = ∅) = (S = ∅ ∧ T = ∅) := fun S T ↦ by
    simp [Set.union_empty_iff]
  have h2 : ¬∀ S : Set Bool, (Sᶜ = ∅) = (S = ∅)ᶜ := fun hc ↦ by
    have := hc {true}
    simp only [eq_iff_iff, compl_iff_not, Set.singleton_ne_empty, not_false_eq_true,
      iff_true] at this
    have hm : false ∈ ({true} : Set Bool)ᶜ := by simp
    rw [this] at hm
    exact hm
  cases s <;> cases t
  · exact le_rfl
  · decide
  · decide
  · exact absurd (h (fun S : Set Bool ↦ S ≠ Set.univ) a1) h1
  · exact le_rfl
  · decide
  · exact absurd (h (fun S : Set Bool ↦ S ≠ Set.univ) a1).1 h1
  · exact absurd (h (fun S : Set Bool ↦ S = ∅) a2).2 h2
  · exact le_rfl

end HoldsFor

/-! ### Truth-valued maps -/

section TruthValued

variable {α : Type*} [BooleanAlgebra α] {f : α → Prop}

/-- A truth-valued map is monotone decreasing exactly when the elements it holds of form a lower
set. -/
theorem holdsFor_weak_iff_isLowerSet : weak.HoldsFor f ↔ IsLowerSet {x | f x} :=
  ⟨fun h _ _ hyx hx ↦ h hyx hx, fun h _ _ hxy hy ↦ h hxy hy⟩

/-- A truth-valued map is anti-additive exactly when the elements it holds of form a lower set
closed under joins, [zwarts-1998]'s quasi-ideal. -/
theorem holdsFor_antiAdditive_iff :
    antiAdditive.HoldsFor f ↔ IsLowerSet {x | f x} ∧ SupClosed {x | f x} :=
  ⟨fun h ↦ ⟨holdsFor_weak_iff_isLowerSet.1 (HoldsFor.of_le h (by decide)),
      fun x hx y hy ↦ (eq_iff_iff.1 (h x y)).2 ⟨hx, hy⟩⟩,
    fun ⟨hl, hs⟩ x y ↦ propext
      ⟨fun hxy ↦ ⟨hl le_sup_left hxy, hl le_sup_right hxy⟩, fun ⟨hx, hy⟩ ↦ hs hx hy⟩⟩

end TruthValued

end Strength

end Negation
