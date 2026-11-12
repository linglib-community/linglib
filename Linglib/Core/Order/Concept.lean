module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.Concept
public import Mathlib.Order.UpperLower.Basic
public import Linglib.Core.Order.Ortholattice

/-!
# Formal concepts: orthocomplements and attribute implication

[UPSTREAM] candidate for `Mathlib/Order/Concept.lean`.

The formal concepts of a symmetric, irreflexive relation `r`, an *orthogonality* relation, form
[an ortholattice](##Concept.instIsOrtholattice). The lattice structure is mathlib's concept
lattice. The orthocomplement [exchanges the extent and the intent](##Concept.intent_compl) of a
concept, as mathlib's `Concept.swap` does between a relation and its converse; for a symmetric
relation the two coincide, which makes it [an order-reversing
involution](##Concept.instInvolutiveCompl).

A concept of a single-sorted relation is determined by its extent, so concepts coerce to sets:
meets are intersections, [joins are extent closures of unions](##Concept.coe_sup), and the object
concept of `a` is the least concept containing `a`.

For any relation, the object concept of `a` lies below that of `a'` exactly when [every attribute
of `a'` is one of `a`](##Concept.ofObject_le_ofObject_iff), and the attribute concept of `b` lies
below that of `a` exactly when [every object with `b` has
`a`](##Concept.ofAttribute_le_ofAttribute_iff), the attribute implication from `b` to `a`. A
preorder on the attributes [reverses along the attribute
concepts](##Concept.antitone_ofAttribute_iff) exactly when each object's attributes form a lower
set of it.

## References

* [holliday-mandelkern-2024]
* [birkhoff-1940]
-/

@[expose] public section

open Order Set

namespace Order

variable {S : Type*} (r : S → S → Prop)

theorem upperPolar_eq_lowerPolar [Std.Symm r] (s : Set S) :
    upperPolar r s = lowerPolar r s := by
  rw [← upperPolar_swap, Std.Symm.swap_eq]

/-- For a symmetric relation the intents are the extents. -/
theorem isIntent_iff_isExtent [Std.Symm r] {s : Set S} : IsIntent r s ↔ IsExtent r s := by
  rw [IsIntent, IsExtent, funext (upperPolar_eq_lowerPolar r)]

theorem isExtent_upperPolar [Std.Symm r] (s : Set S) : IsExtent r (upperPolar r s) :=
  (isIntent_iff_isExtent r).1 isIntent_upperPolar

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

/-- The orthocomplement of a concept exchanges its extent and its intent, as `Concept.swap` does;
for a symmetric relation the result is again a concept of `r`. -/
instance instCompl [Std.Symm r] : Compl (Concept S S r) where
  compl c :=
    { extent := c.intent
      intent := c.extent
      upperPolar_extent := (Order.upperPolar_eq_lowerPolar r _).trans c.lowerPolar_intent
      lowerPolar_intent := (Order.upperPolar_eq_lowerPolar r _).symm.trans c.upperPolar_extent }

@[simp] theorem extent_compl [Std.Symm r] (c : Concept S S r) : cᶜ.extent = c.intent := rfl

@[simp] theorem intent_compl [Std.Symm r] (c : Concept S S r) : cᶜ.intent = c.extent := rfl

/-- A concept of a single-sorted relation is determined by its extent, so concepts
form a `SetLike` family with `↑c = c.extent`. (No `PartialOrder` diamond: `SetLike`
supplies only `Membership`/coercions, and `Concept`'s order is already `extent`-lifted.) -/
instance instSetLike {r : S → S → Prop} : SetLike (Concept S S r) S where
  coe c := c.extent
  coe_injective _ _ h := extent_injective h

/-- The order on concepts is inclusion of extents, so `SetLike.coe_subset_coe` applies. -/
instance {r : S → S → Prop} : IsConcreteLE (Concept S S r) S where
  le_iff := extent_subset_extent_iff.symm

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

theorem mem_compl_iff [Std.Symm r] {c : Concept S S r} {a : S} : a ∈ cᶜ ↔ ∀ ⦃b⦄, b ∈ c → r b a := by
  rw [← SetLike.mem_coe, coe_compl]
  rfl

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
([holliday-mandelkern-2024] Proposition 4.8, where the result is credited to [birkhoff-1940]). -/
instance instInvolutiveCompl [Std.Symm r] : InvolutiveCompl (Concept S S r) where
  compl_compl _ := Concept.ext rfl
  compl_le_compl h := intent_subset_intent_iff.2 h

/-- The concepts of a symmetric, irreflexive relation form an orthocomplemented
lattice ([holliday-mandelkern-2024] Proposition 4.8, where the result is credited to
[birkhoff-1940]). The lattice structure
is mathlib's concept lattice; only the orthocomplement and its axioms are new. -/
instance instIsOrtholattice [Std.Symm r] [Std.Irrefl r] :
    IsOrtholattice (Concept S S r) where
  inf_compl_le_bot _ := fun x hx ↦ absurd (rel_extent_intent hx.1 hx.2) (Std.Irrefl.irrefl x)

/-! ### Object and attribute concepts of any relation -/

section Implication

variable {α β : Type*} {r : α → β → Prop}

/-- The extent of the object concept of `a` is the objects with every attribute of `a`. -/
theorem mem_extent_ofObject_iff {a a' : α} :
    a' ∈ (ofObject r a).extent ↔ ∀ ⦃b⦄, r a b → r a' b := by
  simp [mem_lowerPolar_iff, mem_upperPolar_iff]

/-- The intent of the attribute concept of `b` is the attributes of every object with `b`. -/
theorem mem_intent_ofAttribute_iff {b b' : β} :
    b' ∈ (ofAttribute r b).intent ↔ ∀ ⦃a⦄, r a b → r a b' := by
  simp [mem_lowerPolar_iff, mem_upperPolar_iff]

/-- The object concept of `a` lies below that of `a'` exactly when every attribute of `a'` is
one of `a`. -/
theorem ofObject_le_ofObject_iff {a a' : α} :
    ofObject r a ≤ ofObject r a' ↔ ∀ ⦃b⦄, r a' b → r a b := by
  rw [ofObjects_le_iff, singleton_subset_iff, mem_extent_ofObject_iff]

/-- The attribute concept of `b` lies below that of `a` exactly when every object with `b`
has `a`. -/
theorem ofAttribute_le_ofAttribute_iff {a b : β} :
    ofAttribute r b ≤ ofAttribute r a ↔ ∀ ⦃x⦄, r x b → r x a := by
  rw [le_ofAttributes_iff, singleton_subset_iff, mem_intent_ofAttribute_iff]

/-- The object concepts follow a preorder on the objects exactly when the objects with each
attribute form a lower set of it. -/
theorem monotone_ofObject_iff [Preorder α] :
    Monotone (ofObject r) ↔ ∀ b, IsLowerSet {a | r a b} := by
  simp only [Monotone, ofObject_le_ofObject_iff, IsLowerSet, Set.mem_ofPred_eq]
  exact ⟨fun h _ _ _ hab hb ↦ h hab hb, fun h _ _ hab _ hb ↦ h _ hab hb⟩

/-- The attribute concepts reverse a preorder on the attributes exactly when the attributes of
every object form a lower set of it. -/
theorem antitone_ofAttribute_iff [Preorder β] :
    Antitone (ofAttribute r) ↔ ∀ x, IsLowerSet {b | r x b} := by
  simp only [Antitone, ofAttribute_le_ofAttribute_iff, IsLowerSet, Set.mem_ofPred_eq]
  exact ⟨fun h _ _ _ hab hb ↦ h hab hb, fun h _ _ hab _ hb ↦ h _ hab hb⟩

end Implication

end Concept
