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

This file defines the strengths of negation a context can carry, Zwarts's hierarchy of monotone
decreasing, anti-additive and antimorphic contexts, which are van der Wouden's minimal, regular and
classical negation. A map between Boolean algebras is *monotone decreasing* if it reverses the
order, *anti-additive* if `f (x ⊔ y) = f x ⊓ f y`, and *antimorphic* if it is anti-additive and
`f xᶜ = (f x)ᶜ`, as clausal negation is. Each class contains the next, and the order on the three
strengths is that inclusion. A truth-valued map is monotone decreasing when the elements it holds
of form a lower set, and anti-additive when that lower set is also closed under joins.

## Main definitions

* `Negation.Strength`: the three strengths, a chain.
* `Negation.HasStrength`: a map has a strength.

## Main results

* `Negation.HasStrength.of_le`: a map of a strength has every weaker strength.
* `Negation.Strength.le_iff_forall_hasStrength`: one strength is below another exactly when every
  map of the second has the first.
* `Negation.hasStrength_antiAdditive_iff_supClosed`: a truth-valued map is anti-additive exactly
  when the elements it holds of form a lower set closed under joins.

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

/-- The three strengths of negation. A map is `monotoneDecreasing` if it reverses the order,
`antiAdditive` if it also sends joins to meets, as *nobody* does, and `antimorphic` if it also
commutes with complement, as clausal negation does. -/
inductive Strength where
  | monotoneDecreasing
  | antiAdditive
  | antimorphic
  deriving DecidableEq, Repr, Fintype

namespace Strength

/-- Rank in the chain `monotoneDecreasing < antiAdditive < antimorphic`. -/
def toNat : Strength → ℕ
  | .monotoneDecreasing => 0
  | .antiAdditive => 1
  | .antimorphic => 2

theorem toNat_injective : Function.Injective toNat := by decide

/-- The Zwarts hierarchy as the linear order `monotoneDecreasing < antiAdditive < antimorphic`. -/
instance : LinearOrder Strength :=
  LinearOrder.lift' toNat toNat_injective

instance : BoundedOrder Strength where
  bot := monotoneDecreasing
  bot_le := by decide
  top := antimorphic
  le_top := by decide

@[simp] theorem bot_eq_monotoneDecreasing : (⊥ : Strength) = monotoneDecreasing := rfl

@[simp] theorem top_eq_antimorphic : (⊤ : Strength) = antimorphic := rfl

@[simp] theorem monotoneDecreasing_le (s : Strength) : monotoneDecreasing ≤ s := bot_le

@[simp] theorem le_antimorphic (s : Strength) : s ≤ antimorphic := le_top

@[simp] theorem le_monotoneDecreasing_iff {s : Strength} :
    s ≤ monotoneDecreasing ↔ s = monotoneDecreasing :=
  le_bot_iff

end Strength

open Strength

/-! ### The maps of a strength -/

section HasStrength

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β] {s t : Strength} {f : α → β}

/-- A map has a strength of negation: it is monotone decreasing, anti-additive, or antimorphic
([zwarts-1998]'s (91), (107) and (114)). -/
def HasStrength (f : α → β) : Strength → Prop
  | monotoneDecreasing => Antitone f
  | antiAdditive => ∀ x y, f (x ⊔ y) = f x ⊓ f y
  | antimorphic => (∀ x y, f (x ⊔ y) = f x ⊓ f y) ∧ ∀ x, f xᶜ = (f x)ᶜ

@[simp] theorem hasStrength_monotoneDecreasing : HasStrength f monotoneDecreasing ↔ Antitone f :=
  Iff.rfl

@[simp] theorem hasStrength_antiAdditive :
    HasStrength f antiAdditive ↔ ∀ x y, f (x ⊔ y) = f x ⊓ f y :=
  Iff.rfl

@[simp] theorem hasStrength_antimorphic :
    HasStrength f antimorphic ↔ (∀ x y, f (x ⊔ y) = f x ⊓ f y) ∧ ∀ x, f xᶜ = (f x)ᶜ :=
  Iff.rfl

private theorem antitone_of_map_sup (h : ∀ x y, f (x ⊔ y) = f x ⊓ f y) : Antitone f :=
  Monotone.of_map_sup (β := βᵒᵈ) h

/-- A map of a strength has every weaker strength. -/
theorem HasStrength.of_le (h : HasStrength f t) (hst : s ≤ t) : HasStrength f s := by
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

/-- An antimorphic map sends `⊤` to `⊥`. -/
theorem HasStrength.map_top (h : HasStrength f antimorphic) : f ⊤ = ⊥ := by
  rw [← sup_compl_eq_top (x := ⊥), h.1, h.2, inf_compl_self]

/-- An antimorphic map sends `⊥` to `⊤`. -/
theorem HasStrength.map_bot (h : HasStrength f antimorphic) : f ⊥ = ⊤ := by
  rw [← compl_top, h.2, h.map_top, compl_bot]

/-- One strength is below another exactly when every map of the second has the first. -/
theorem Strength.le_iff_forall_hasStrength :
    s ≤ t ↔ ∀ f : Set Bool → Prop, HasStrength f t → HasStrength f s := by
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

end HasStrength

/-! ### Truth-valued maps -/

section TruthValued

variable {α : Type*} [BooleanAlgebra α] {f : α → Prop}

/-- A truth-valued map is monotone decreasing exactly when the elements it holds of form a lower
set. -/
theorem hasStrength_monotoneDecreasing_iff_isLowerSet :
    HasStrength f monotoneDecreasing ↔ IsLowerSet {x | f x} :=
  ⟨fun h _ _ hyx hx ↦ h hyx hx, fun h _ _ hxy hy ↦ h hxy hy⟩

/-- A truth-valued map is anti-additive exactly when the elements it holds of form a lower set
closed under joins, [zwarts-1998]'s quasi-ideal. -/
theorem hasStrength_antiAdditive_iff_supClosed :
    HasStrength f antiAdditive ↔ IsLowerSet {x | f x} ∧ SupClosed {x | f x} :=
  ⟨fun h ↦ ⟨hasStrength_monotoneDecreasing_iff_isLowerSet.1 (HasStrength.of_le h (by decide)),
      fun x hx y hy ↦ (eq_iff_iff.1 (h x y)).2 ⟨hx, hy⟩⟩,
    fun ⟨hl, hs⟩ x y ↦ propext
      ⟨fun hxy ↦ ⟨hl le_sup_left hxy, hl le_sup_right hxy⟩, fun ⟨hx, hy⟩ ↦ hs hx hy⟩⟩

end TruthValued

/-! ### Composites with negation

A map that preserves meets, applied after complement, is anti-additive, and it is antimorphic
only if it also commutes with complement. Complement applied after a monotone map is monotone
decreasing, and it is anti-additive only if the map preserves joins. -/

section Composite

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β] {f g : α → β}

private theorem map_sup_of_map_inf_of_map_compl (hg : ∀ x y, g (x ⊓ y) = g x ⊓ g y)
    (hc : ∀ x, g xᶜ = (g x)ᶜ) (x y : α) : g (x ⊔ y) = g x ⊔ g y := by
  rw [← compl_compl (x ⊔ y), hc, compl_sup, hg, hc, hc, ← compl_sup, compl_compl]

variable {ι : Type*} {α β : ι → Type*} [∀ i, BooleanAlgebra (α i)] [∀ i, BooleanAlgebra (β i)]
  {s : Strength} {f g : ∀ i, α i → β i}

/-- Maps that preserve meets, applied after complement, not all of them commuting with complement,
have exactly the strengths up to anti-additive. -/
theorem forall_hasStrength_iff_le_antiAdditive (hfg : ∀ i, f i = g i ∘ compl)
    (hg : ∀ i x y, g i (x ⊓ y) = g i x ⊓ g i y) (hn : ∃ i, ¬∀ x, f i xᶜ = (f i x)ᶜ) :
    (∀ i, HasStrength (f i) s) ↔ s ≤ antiAdditive := by
  have haa : ∀ i x y, f i (x ⊔ y) = f i x ⊓ f i y := fun i x y ↦ by
    simp only [hfg, Function.comp_apply, compl_sup, hg]
  cases s
  · exact iff_of_true (fun i ↦ HasStrength.of_le (t := antiAdditive) (haa i) (by decide))
      (by decide)
  · exact iff_of_true haa le_rfl
  · exact iff_of_false (fun h ↦ hn.elim fun i hi ↦ hi (h i).2) (by decide)

/-- Maps that preserve meets and not all of them joins, applied after complement, have exactly the
strengths up to anti-additive. -/
theorem forall_hasStrength_iff_le_antiAdditive_of_not_map_sup (hfg : ∀ i, f i = g i ∘ compl)
    (hg : ∀ i x y, g i (x ⊓ y) = g i x ⊓ g i y)
    (hn : ∃ i, ¬∀ x y, g i (x ⊔ y) = g i x ⊔ g i y) :
    (∀ i, HasStrength (f i) s) ↔ s ≤ antiAdditive :=
  forall_hasStrength_iff_le_antiAdditive hfg hg <| hn.imp fun i hi hc ↦
    hi (map_sup_of_map_inf_of_map_compl (hg i) fun x ↦ by simpa [hfg] using hc xᶜ)

/-- Complement applied after monotone maps, not all of them preserving joins, is monotone
decreasing and no stronger. -/
theorem forall_hasStrength_iff_le_monotoneDecreasing (hfg : ∀ i, f i = compl ∘ g i)
    (hg : ∀ i, Monotone (g i)) (hn : ∃ i, ¬∀ x y, g i (x ⊔ y) = g i x ⊔ g i y) :
    (∀ i, HasStrength (f i) s) ↔ s ≤ monotoneDecreasing := by
  have key : ∀ i, (∀ x y, f i (x ⊔ y) = f i x ⊓ f i y) → ∀ x y, g i (x ⊔ y) = g i x ⊔ g i y :=
    fun i h x y ↦ compl_injective (by simpa [hfg] using h x y)
  cases s
  · exact iff_of_true (fun i ↦ hfg i ▸ fun _ _ hab ↦ compl_le_compl (hg i hab)) le_rfl
  · exact iff_of_false (fun h ↦ hn.elim fun i hi ↦ hi (key i (h i))) (by decide)
  · exact iff_of_false (fun h ↦ hn.elim fun i hi ↦ hi (key i (h i).1)) (by decide)

end Composite

end Negation
