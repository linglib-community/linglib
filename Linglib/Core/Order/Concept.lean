module

public import Mathlib.Data.Fintype.Defs
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

A concept of a single-sorted relation is determined by its extent, so concepts coerce to sets:
meets are intersections, joins are extent closures of unions, and the object concept of `a` is
the least concept containing `a`, whose members are the `b` related to everything `a` is.

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
* `Concept.coe_sup`, `Concept.coe_compl`: joins and orthocomplements as sets.
* `Concept.mem_ofObject_iff`: the members of an object concept.
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

variable {r} in
theorem IsExtent.upperPolar_upperPolar [Std.Symm r] {s : Set S} (hs : IsExtent r s) :
    upperPolar r (upperPolar r s) = s := by
  rw [upperPolar_eq_lowerPolar r (upperPolar r s)]
  exact hs.eq

section Decidable

variable {α β : Type*} {r : α → β → Prop} {s : Set α} {t : Set β}

theorem isExtent_iff_lowerPolar_upperPolar_subset :
    IsExtent r s ↔ lowerPolar r (upperPolar r s) ⊆ s :=
  isExtent_iff.trans ⟨Eq.subset, fun h ↦ h.antisymm (subset_lowerPolar_upperPolar r s)⟩

variable [∀ a b, Decidable (r a b)]

instance [Fintype α] [DecidablePred (· ∈ s)] (b : β) : Decidable (b ∈ upperPolar r s) :=
  inferInstanceAs (Decidable (∀ a, a ∈ s → r a b))

instance [Fintype β] [DecidablePred (· ∈ t)] (a : α) : Decidable (a ∈ lowerPolar r t) :=
  inferInstanceAs (Decidable (∀ b, b ∈ t → r a b))

instance [Fintype α] [Fintype β] [DecidablePred (· ∈ s)] (a : α) :
    Decidable (a ∈ extentClosure r s) :=
  inferInstanceAs (Decidable (a ∈ lowerPolar r (upperPolar r s)))

instance [Fintype α] [Fintype β] [DecidablePred (· ∈ s)] : Decidable (IsExtent r s) :=
  decidable_of_iff (∀ a, a ∈ lowerPolar r (upperPolar r s) → a ∈ s)
    isExtent_iff_lowerPolar_upperPolar_subset.symm

end Decidable

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

theorem extent_bot_eq_empty [Std.Irrefl r] : (⊥ : Concept S S r).extent = ∅ :=
  Set.disjoint_univ.1 (Concept.intent_bot (r := r) ▸ (⊥ : Concept S S r).disjoint_extent_intent)

section SetLike

variable {r}

@[simp] theorem coe_inf (c d : Concept S S r) :
    ((c ⊓ d : Concept S S r) : Set S) = (c : Set S) ∩ d := rfl

@[simp] theorem coe_top : ((⊤ : Concept S S r) : Set S) = univ := rfl

@[simp] theorem coe_bot [Std.Irrefl r] : ((⊥ : Concept S S r) : Set S) = ∅ :=
  extent_bot_eq_empty r

@[simp] theorem coe_eq_empty [Std.Irrefl r] {c : Concept S S r} : (c : Set S) = ∅ ↔ c = ⊥ := by
  rw [← coe_bot (r := r), SetLike.coe_set_eq]

@[simp] theorem coe_compl [Std.Symm r] (c : Concept S S r) :
    ((cᶜ : Concept S S r) : Set S) = upperPolar r c :=
  c.upperPolar_extent.symm

/-- The join of two concepts is the extent closure of the union of their extents. -/
@[simp] theorem coe_sup (c d : Concept S S r) :
    ((c ⊔ d : Concept S S r) : Set S) = extentClosure r (c ∪ d) := by
  show (c ⊔ d).extent = _
  rw [extent_sup, extentClosure_apply, upperPolar_union, ← c.upperPolar_extent,
    ← d.upperPolar_extent]
  rfl

@[simp] theorem coe_iInf {ι : Sort*} (f : ι → Concept S S r) :
    ((⨅ i, f i : Concept S S r) : Set S) = ⋂ i, (f i : Set S) :=
  extent_iInf f

@[simp] theorem coe_iSup {ι : Sort*} (f : ι → Concept S S r) :
    ((⨆ i, f i : Concept S S r) : Set S) = extentClosure r (⋃ i, (f i : Set S)) := by
  show (⨆ i, f i).extent = _
  rw [extent_iSup, extentClosure_apply, upperPolar_iUnion]
  simp only [← upperPolar_extent]
  rfl

/-! ### Object concepts -/

@[simp] theorem coe_ofObject (a : S) : (ofObject r a : Set S) = extentClosure r {a} := rfl

/-- The object concept of `a` is the least concept containing `a`. -/
theorem ofObject_le_iff {a : S} {c : Concept S S r} : ofObject r a ≤ c ↔ a ∈ c :=
  ofObjects_le_iff.trans singleton_subset_iff

theorem mem_ofObject_self (a : S) : a ∈ ofObject r a :=
  ofObject_le_iff.1 le_rfl

theorem mem_ofObject_iff {a b : S} : b ∈ ofObject r a ↔ ∀ ⦃x⦄, r a x → r b x := by
  change b ∈ (ofObject r a).extent ↔ _
  simp [mem_lowerPolar_iff, mem_upperPolar_iff]

theorem mem_compl_ofObject_iff [Std.Symm r] {a b : S} : b ∈ (ofObject r a)ᶜ ↔ r a b := by
  change b ∈ (ofObject r a).intent ↔ _
  simp [mem_upperPolar_iff]

/-- An extent containing `a` contains the object concept of `a`. -/
theorem _root_.Order.IsExtent.mem_of_mem_ofObject {s : Set S} (hs : IsExtent r s) {a b : S}
    (hb : b ∈ ofObject r a) (ha : a ∈ s) : b ∈ s :=
  extent_subset_extent_iff.2 ((ofObject_le_iff (c := ofIsExtent r s hs)).2 ha) hb

end SetLike

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
