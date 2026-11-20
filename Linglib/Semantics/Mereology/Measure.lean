module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.BooleanAlgebra.Basic
public import Linglib.Semantics.Mereology.Classical

/-!
# Extensive measures

An extensive measure on a generalized Boolean algebra of individuals is a function `μ` into an
ordered additive monoid with `μ (x ⊔ y) = μ x + μ y` for disjoint `x` and `y` and `0 < μ x` for
`x ≠ ⊥`. The whole then measures the part plus the remainder,
`μ y = μ x + μ (y \ x)`, so `μ` is strictly monotone where addition is
(`Mereology.IsExtensive.strictMono`), and the individuals of a region with a given measure are
quantized (`Mereology.qua_inter_preimage_of_strictMonoOn`), as *five ounces of gold* is. The
number of members is an extensive measure of finite sets (`Mereology.isExtensive_card`), and
the extended number of members one of sets (`Mereology.isExtensive_encard`). The atom count is
likewise strictly monotone on sums of atoms, which quantizes *two cats*
(`Mereology.qua_supClosure_inter_atomCount`).

## Implementation notes

`IsExtensive` is a predicate on a function, as `Monotone` is, and not a class: a carrier has
many extensive measures. The carrier is a generalized Boolean algebra, where the remainder of a
part in a whole is `y \ x` and non-overlap is `Disjoint`; [krifka-1989] assumes relative
complements of his part structures for the same purpose. Addition on `ℕ∞` is not strictly
monotone, so `Set.encard` is strictly monotone on finite sets only.

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

theorem atomCount_strictMonoOn [SemilatticeSup α] [Fintype α] {s : Set α}
    (hs : ∀ ⦃a⦄, a ∈ s → Atom a) : StrictMonoOn (atomCount α) (supClosure s) := by
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
theorem qua_supClosure_inter_atomCount [SemilatticeSup α] [Fintype α] {s : Set α}
    (hs : ∀ ⦃a⦄, a ∈ s → Atom a) (n : ℕ) : QUA (supClosure s ∩ atomCount α ⁻¹' {n}) :=
  qua_inter_preimage_of_strictMonoOn (atomCount_strictMonoOn hs) n

section Extensive

variable {M : Type*} [GeneralizedBooleanAlgebra α] [AddCommMonoid M] [PartialOrder M] {μ : α → M}

/-- An extensive measure ([krifka-1989], [krifka-1998]) is additive over disjoint individuals
and positive on the ones that are not null. -/
structure IsExtensive (μ : α → M) : Prop where
  /-- The measure of a sum of disjoint individuals is the sum of their measures. -/
  map_sup_of_disjoint ⦃x y : α⦄ : Disjoint x y → μ (x ⊔ y) = μ x + μ y
  /-- An individual that is not null has a positive measure. -/
  pos ⦃x : α⦄ : x ≠ ⊥ → 0 < μ x

/-- The measure of a whole is the measure of a part plus that of the remainder. -/
theorem IsExtensive.map_eq_add_sdiff (h : IsExtensive μ) {x y : α} (hxy : x ≤ y) :
    μ y = μ x + μ (y \ x) := by
  rw [← h.map_sup_of_disjoint disjoint_sdiff_self_right, sup_sdiff_cancel_right hxy]

/-- An extensive measure gives a proper part a smaller measure than the whole. -/
theorem IsExtensive.strictMono [AddLeftStrictMono M] (h : IsExtensive μ) : StrictMono μ :=
  fun x y hxy ↦ by
    rw [h.map_eq_add_sdiff hxy.le]
    exact lt_add_of_pos_right _ (h.pos fun h0 ↦ hxy.not_ge (sdiff_eq_bot_iff.1 h0))

end Extensive

theorem isExtensive_card [DecidableEq β] : IsExtensive (Finset.card : Finset β → ℕ) where
  map_sup_of_disjoint _ _ h := Finset.card_union_of_disjoint h
  pos _ h := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h)

theorem isExtensive_encard : IsExtensive (Set.encard : Set β → ℕ∞) where
  map_sup_of_disjoint _ _ h := Set.encard_union_eq h
  pos _ h := Set.encard_pos.2 (Set.nonempty_iff_ne_empty.2 h)

end Mereology
