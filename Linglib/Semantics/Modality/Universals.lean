module

public import Linglib.Semantics.Modality.Typology

/-!
# Semantic universals for modal meanings

This file defines the two proposed universals on modal meanings, sets of force-flavor pairs, as
predicates on a finite set of pairs, and the weaker property proposed as a fallback. A meaning has
independent force and flavor when it is the product of its forces and its flavors
([steinert-threlkeld-imel-guo-2023]), it varies on a single axis when its pairs all share a
force or all share a flavor ([nauze-2008]), and it is path-connected when any two of its pairs
recombine in at least one order. A single-axis meaning is a product, and a product is
path-connected.

On a Kratzer semantics ([kratzer-1981]) a modal's force and its flavor are set by separate
parameters, so its meaning is a product and satisfies the universal; a fixed-force modal ranging
over flavors, or a variable-force modal of one flavor, varies on a single axis besides.

The forces and flavors are any two types, since [steinert-threlkeld-imel-guo-2023] leave open
what the axes are: a modal's meaning is a `Finset ForceFlavor`, and an attitude verb's pairs its
force with a flavor of its own, doxastic or assertive for Koryak *ivək*
([mocnik-abramovitz-2019]).

## Main definitions

* `Modality.ForceFlavorIndependent`: the meaning is the product of its projections.
* `Modality.SingleAxis`: at most one force or at most one flavor.
* `Modality.PathConnected`: closure under recombining two pairs in at least one order.

## Main results

* `Modality.forceFlavorIndependent_iff`: the universal as stated, closure under
  recombining the force of one pair with the flavor of another.
* `Modality.forceFlavorIndependent_iff_pair_product_subset`: independence is convexity
  for the grid betweenness of [chemla-buccola-dautriche-2019].
* `Modality.SingleAxis.forceFlavorIndependent`,
  `Modality.ForceFlavorIndependent.pathConnected`: the three properties in order of
  strength.
* `Modality.forceFlavorIndependent_product`: a product meaning satisfies the universal.
* `Modality.ModalItem.singleAxis_meaning_iff`: an item varies on a single axis when it does not
  vary in both force and flavor.

## References

* [steinert-threlkeld-imel-guo-2023]
* [nauze-2008]
* [kratzer-1981]
* [chemla-buccola-dautriche-2019]
* [mocnik-abramovitz-2019]
-/

@[expose] public section

namespace Modality

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (m : Finset (α × β))

/-- A meaning has independent force and flavor when it is the product of its forces and its
flavors, so that with `(fo₁, fl₁)` and `(fo₂, fl₂)` it expresses `(fo₁, fl₂)`. -/
def ForceFlavorIndependent : Prop := m = m.image Prod.fst ×ˢ m.image Prod.snd

/-- A meaning varies on a single axis when its pairs all share a force or all share a flavor. -/
def SingleAxis : Prop := (m.image Prod.fst).card ≤ 1 ∨ (m.image Prod.snd).card ≤ 1

/-- A meaning is path-connected when with `(fo₁, fl₁)` and `(fo₂, fl₂)` it expresses `(fo₁, fl₂)`
or `(fo₂, fl₁)`, the Ferrers property of a relation. -/
def PathConnected : Prop := ∀ x ∈ m, ∀ y ∈ m, (x.1, y.2) ∈ m ∨ (y.1, x.2) ∈ m

instance : Decidable (ForceFlavorIndependent m) := inferInstanceAs (Decidable (_ = _))

instance : Decidable (SingleAxis m) := inferInstanceAs (Decidable (_ ∨ _))

instance : Decidable (PathConnected m) :=
  inferInstanceAs (Decidable (∀ x ∈ m, ∀ y ∈ m, (x.1, y.2) ∈ m ∨ (y.1, x.2) ∈ m))

variable {m}

/-- The universal as the paper states it, closure under recombining two pairs into a third. -/
theorem forceFlavorIndependent_iff :
    ForceFlavorIndependent m ↔ ∀ x ∈ m, ∀ y ∈ m, (x.1, y.2) ∈ m := by
  refine ⟨fun h x hx y hy ↦ ?_, fun h ↦ Finset.subset_product.antisymm fun ⟨a, b⟩ hz ↦ ?_⟩
  · rw [ForceFlavorIndependent] at h
    rw [h]
    exact Finset.mk_mem_product (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy)
  · simp only [Finset.mem_product, Finset.mem_image] at hz
    obtain ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩ := hz
    exact h x hx y hy

alias ⟨ForceFlavorIndependent.mk_mem, ForceFlavorIndependent.of_mk_mem⟩ :=
  forceFlavorIndependent_iff

/-- A meaning is independent exactly when it contains the rectangle spanned by any two of its
pairs, the pairs between them for the grid betweenness on the force-flavor space, so
independence is convexity in that sense. -/
theorem forceFlavorIndependent_iff_pair_product_subset :
    ForceFlavorIndependent m ↔ ∀ x ∈ m, ∀ y ∈ m,
      ({x.1, y.1} : Finset α) ×ˢ ({x.2, y.2} : Finset β) ⊆ m := by
  rw [forceFlavorIndependent_iff]
  refine ⟨fun h x hx y hy ⟨a, b⟩ hz ↦ ?_,
    fun h x hx y hy ↦ h x hx y hy (Finset.mk_mem_product (by simp) (by simp))⟩
  simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hz
  obtain ⟨rfl | rfl, rfl | rfl⟩ := hz
  exacts [hx, h x hx y hy, h y hy x hx, hy]

theorem SingleAxis.forceFlavorIndependent (h : SingleAxis m) : ForceFlavorIndependent m := by
  refine .of_mk_mem fun x hx y hy ↦ ?_
  rcases h with h | h
  · rw [Finset.card_le_one.1 h _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)]
    exact hy
  · rw [← Finset.card_le_one.1 h _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)]
    exact hx

theorem ForceFlavorIndependent.pathConnected (h : ForceFlavorIndependent m) : PathConnected m :=
  fun x hx y hy ↦ Or.inl (h.mk_mem x hx y hy)

theorem ForceFlavorIndependent.singleton (x : α × β) : ForceFlavorIndependent {x} := by
  simp [ForceFlavorIndependent]

/-- A modal item varies on a single axis exactly when it does not vary in both force and
flavor. -/
theorem ModalItem.singleAxis_meaning_iff {i : ModalItem} :
    SingleAxis i.meaning ↔ ¬ (i.VariesForce ∧ i.VariesFlavor) := by
  unfold SingleAxis ModalItem.VariesForce ModalItem.VariesFlavor ModalItem.forces ModalItem.flavors
  omega

/-! ### Kratzer modals

A modal whose force and flavor are set by separate parameters expresses a product. -/

variable (F : Finset α) (Φ : Finset β)

theorem forceFlavorIndependent_product : ForceFlavorIndependent (F ×ˢ Φ) :=
  .of_mk_mem fun _ hx _ hy ↦
    Finset.mk_mem_product (Finset.mem_product.1 hx).1 (Finset.mem_product.1 hy).2

theorem singleAxis_singleton_product (fo : α) : SingleAxis ({fo} ×ˢ Φ) :=
  Or.inl ((Finset.card_le_card Finset.subset_product_image_fst).trans_eq (Finset.card_singleton fo))

theorem singleAxis_product_singleton (fl : β) : SingleAxis (F ×ˢ {fl}) :=
  Or.inr ((Finset.card_le_card Finset.subset_product_image_snd).trans_eq (Finset.card_singleton fl))

end Modality
