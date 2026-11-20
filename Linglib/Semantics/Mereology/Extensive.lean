module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Set.Card
public import Linglib.Semantics.Mereology.Basic
public import Linglib.Semantics.Mereology.Fusion

/-!
# Extensive measures

An extensive measure on a part structure with binary sums and no null element is a function
`μ` into an ordered additive monoid with `μ (x ⊔ y) = μ x + μ y` for `x` and `y` that do not
overlap and `0 < μ x` for every `x`. Under Additive Remainder, where every proper part `x` of
`y` has a `z` that does not overlap `x` with `x ⊔ z = y`, the whole measures more than the part
(`Mereology.IsExtensive.strictMono`). The individuals of a region with a given value of a
function that is strictly monotone there are quantized
(`Mereology.qua_inter_preimage_of_strictMonoOn`), as *five ounces of gold* is. The atom count
is strictly monotone on sums of atoms, which quantizes *two cats*
(`Mereology.qua_supClosure_inter_atomCount`).

## Implementation notes

`IsExtensive` is a predicate on a function, as `Monotone` is, and not a class: a carrier has
many extensive measures. Additive Remainder is the relative complement that [krifka-1989]
assumes of his part structures, existence without uniqueness, which does not make the structure
distributive. On a generalized Boolean algebra, which has a null element, the facts that play
these roles are mathlib's: `Finset.card` is additive on disjoint sets
(`Finset.card_union_of_disjoint`) and strictly monotone (`Finset.card_strictMono`).

## References

* [champollion-krifka-2016], [krifka-1989], [krifka-1998]
-/

@[expose] public section

namespace Mereology

variable {α β : Type*}

/-! ### Extensive measures

[krifka-1989] and [krifka-1998] define an extensive measure by additivity over non-overlapping
elements and positivity, and derive from the remainder principle that a proper part measures less
than the whole. [champollion-krifka-2016] call a measure extensive on a set when it has that
property there. Either way, the measure phrases such a measure builds are quantized. -/

/-- The members of a region with measure `n` are quantized if the measure is strictly monotone on
the region, as *five ounces of gold* is in the measure construction of [krifka-1989]. -/
theorem qua_inter_preimage_of_strictMonoOn {M : Type*} [PartialOrder α] [Preorder M] {r : Set α}
    {μ : α → M} (hμ : StrictMonoOn μ r) (n : M) : QUA (r ∩ μ ⁻¹' {n}) :=
  fun _ hx _ hy hne hle ↦ (hμ hx.1 hy.1 (lt_of_le_of_ne hle hne)).ne (hx.2.trans hy.2.symm)

theorem atomCount_strictMonoOn [SemilatticeSup α] [OrderBot α] [Fintype α] {s : Set α}
    (hs : ∀ ⦃a⦄, a ∈ s → IsAtom a) : StrictMonoOn (atomCount α) (supClosure s) := by
  intro x _ y hy hxy
  obtain ⟨t, ht, hPt, rfl⟩ := hy
  have hsub : atomsBelow x ⊆ atomsBelow (t.sup' ht id) :=
    fun a ha ↦ ⟨ha.1, ha.2.trans hxy.le⟩
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ t, ¬ a ≤ x := by
    by_contra! hno
    exact hxy.not_ge (Finset.sup'_le ht id hno)
  rw [atomCount_eq_ncard, atomCount_eq_ncard]
  exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2
    ⟨a, ⟨hs (hPt ha), Finset.le_sup' id ha⟩, fun h ↦ hax h.2⟩) (Set.toFinite _)

/-- The sums of `P`-atoms with `n` atoms form an antichain, so *two cats* is quantized
([champollion-krifka-2016]). -/
theorem qua_supClosure_inter_atomCount [SemilatticeSup α] [OrderBot α] [Fintype α] {s : Set α}
    (hs : ∀ ⦃a⦄, a ∈ s → IsAtom a) (n : ℕ) : QUA (supClosure s ∩ atomCount α ⁻¹' {n}) :=
  qua_inter_preimage_of_strictMonoOn (atomCount_strictMonoOn hs) n

section Extensive

variable {M : Type*} [SemilatticeSup α] [AddCommMonoid M] [PartialOrder M] {μ : α → M}

/-- An extensive measure ([krifka-1989], [krifka-1998]) is additive over individuals that do not
overlap and positive. -/
structure IsExtensive (μ : α → M) : Prop where
  /-- The measure of a sum of non-overlapping individuals is the sum of their measures. -/
  map_sup ⦃x y : α⦄ : ¬ Overlap x y → μ (x ⊔ y) = μ x + μ y
  /-- Every individual has a positive measure. -/
  pos (x : α) : 0 < μ x

/-- Under Additive Remainder an extensive measure gives a proper part a smaller measure than
the whole, which adds the measure of a remainder to it. -/
theorem IsExtensive.strictMono [AddLeftStrictMono M] (h : IsExtensive μ)
    (hR : AdditiveRemainder α) : StrictMono μ := fun x y hxy ↦ by
  obtain ⟨z, hz, rfl⟩ := hR hxy
  rw [h.map_sup fun ho ↦ hz ho.symm]
  exact lt_add_of_pos_right _ (h.pos z)

end Extensive

end Mereology
