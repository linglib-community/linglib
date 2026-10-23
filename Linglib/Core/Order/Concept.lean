module

public import Mathlib.Order.Concept
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Core.Order.Ortholattice

/-!
# Formal concepts: orthocomplements and attribute implication

[UPSTREAM] candidate for `Mathlib/Order/Concept.lean`.

The formal concepts of a symmetric, irreflexive relation `r`, an *orthogonality* relation, form an
ortholattice. The lattice structure is mathlib's concept lattice; the new content is the
orthocomplement `Aᶜ = upperPolar r A = {x | ∀ y ∈ A, r x y}`, which for a symmetric relation is an
order-reversing involution on extents.

For any relation, the attribute concept of `b` lies below that of `a` exactly when every object
with `b` has `a`, the attribute implication from `b` to `a`. A preorder on the attributes reverses
along the attribute concepts exactly when each object's attributes form a lower set of it.

## Main definitions

* `Concept.instCompl`: the orthocomplement of a concept, whose extent is the concept's intent.
* `Concept.instSetLike`: a concept of a single-sorted relation is determined by its extent.

## Main results

* `Concept.instInvolutiveCompl`: for a symmetric relation the orthocomplement is an involution.
* `Concept.instIsOrtholattice`: for a symmetric, irreflexive relation the concepts form
  an ortholattice.
* `Concept.ofAttribute_le_ofAttribute_iff`: attribute concepts are ordered by attribute
  implication.
* `Concept.antitone_ofAttribute_iff`: the attribute concepts reverse a preorder exactly when every
  object's attributes form a lower set.

## References

* [holliday-mandelkern-2024]
-/

@[expose] public section

open Order Set

namespace Order

variable {S : Type*} (r : S → S → Prop)

theorem upperPolar_eq_lowerPolar [Std.Symm r] (s : Set S) :
    upperPolar r s = lowerPolar r s := by
  rw [← upperPolar_swap, Std.Symm.swap_eq]

theorem isExtent_upperPolar [Std.Symm r] (s : Set S) : IsExtent r (upperPolar r s) := by
  rw [upperPolar_eq_lowerPolar r]; exact isExtent_lowerPolar

end Order

namespace Concept

variable {S : Type*} (r : S → S → Prop)

/-- The orthocomplement of a concept is the concept whose extent is its intent, well defined
because `r` is symmetric. -/
instance instCompl [Std.Symm r] : Compl (Concept S S r) where
  compl c := .ofIsExtent r c.intent <| c.upperPolar_extent ▸ Order.isExtent_upperPolar r c.extent

@[simp] theorem extent_compl [Std.Symm r] (c : Concept S S r) : cᶜ.extent = c.intent := rfl

@[simp] theorem intent_compl [Std.Symm r] (c : Concept S S r) :
    cᶜ.intent = upperPolar r c.intent := rfl

/-- A concept of a single-sorted relation is determined by its extent, so concepts
form a `SetLike` family with `↑c = c.extent`. (No `PartialOrder` diamond: `SetLike`
supplies only `Membership`/coercions, and `Concept`'s order is already `extent`-lifted.) -/
instance instSetLike {r : S → S → Prop} : SetLike (Concept S S r) S where
  coe c := c.extent
  coe_injective _ _ h := extent_injective h

theorem extent_bot_eq_empty [Std.Irrefl r] : (⊥ : Concept S S r).extent = ∅ := by
  rw [Concept.extent_bot]
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun hx ↦ Std.Irrefl.irrefl x (hx (Set.mem_univ x))

/-- For a symmetric relation the orthocomplement is an involution of the concept lattice
([holliday-mandelkern-2024] Proposition 4.8). -/
instance instInvolutiveCompl [Std.Symm r] : InvolutiveCompl (Concept S S r) where
  compl_compl c := Concept.ext <| by simp [Order.upperPolar_eq_lowerPolar]
  compl_le_compl {c d} h := by
    show d.intent ⊆ c.intent
    rw [← c.upperPolar_extent, ← d.upperPolar_extent]; exact upperPolar_anti r h

/-- The concepts of a symmetric, irreflexive relation form an orthocomplemented
lattice ([holliday-mandelkern-2024] Proposition 4.8). The lattice structure
is mathlib's concept lattice; only the orthocomplement and its axioms are new. -/
instance instIsOrtholattice [Std.Symm r] [Std.Irrefl r] :
    IsOrtholattice (Concept S S r) where
  inf_compl_le_bot _ := fun x hx ↦ absurd (rel_extent_intent hx.1 hx.2) (Std.Irrefl.irrefl x)

/-! ### Attribute implication -/

section Implication

variable {α β : Type*} {r : α → β → Prop} {a b : β}

/-- The attribute concept of `b` lies below that of `a` exactly when every object with `b`
has `a`. -/
theorem ofAttribute_le_ofAttribute_iff :
    ofAttribute r b ≤ ofAttribute r a ↔ ∀ ⦃x⦄, r x b → r x a := by
  rw [← extent_subset_extent_iff]
  simp [ofAttribute, ofAttributes, Set.subset_def, mem_lowerPolar_iff]

/-- The attribute concepts reverse a preorder on the attributes exactly when the attributes of
every object form a lower set of it. -/
theorem antitone_ofAttribute_iff [Preorder β] :
    Antitone (ofAttribute r) ↔ ∀ x, IsLowerSet {b | r x b} := by
  simp only [Antitone, ofAttribute_le_ofAttribute_iff, IsLowerSet, Set.mem_ofPred_eq]
  exact ⟨fun h _ _ _ hab hb ↦ h hab hb, fun h _ _ hab _ hb ↦ h _ hab hb⟩

end Implication

end Concept
