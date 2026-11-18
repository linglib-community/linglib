module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Linglib.Semantics.Mereology.Classical

/-!
# Extensive measures

An extensive measure is additive over non-overlapping individuals and positive on non-null
ones. Over a carrier with remainders it is
[strictly monotone](##Mereology.IsExtensiveMeasure.strictMono), so
[the individuals of a given measure are quantized](##Mereology.qua_and_eq_of_strictMonoOn), as
*five ounces of gold* is. The atom count is likewise strictly monotone on sums of atoms, which
[quantizes *two cats*](##Mereology.qua_algClosure_atomCount).

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

/-- The `R`-elements of measure `n` are quantized if the measure is strictly monotone on `R`, as
*five ounces of gold* is in the measure construction of [krifka-1989]. -/
theorem qua_and_eq_of_strictMonoOn {M : Type*} [PartialOrder α] [Preorder M] {R : α → Prop}
    {μ : α → M} (hμ : StrictMonoOn μ {x | R x}) (n : M) : QUA fun x ↦ R x ∧ μ x = n :=
  fun _ hx _ hy hne hle ↦ (hμ hx.1 hy.1 (lt_of_le_of_ne hle hne)).ne (hx.2.trans hy.2.symm)

theorem atomCount_strictMonoOn [SemilatticeSup α] [Fintype α] {P : α → Prop}
    (hP : ∀ ⦃a⦄, P a → Atom a) : StrictMonoOn (atomCount α) {x | AlgClosure P x} := by
  intro x _ y hy hxy
  obtain ⟨t, ht, hPt, rfl⟩ := (algClosure_iff_exists_sup' P y).1 hy
  have hsub : atomsBelow x ⊆ atomsBelow (t.sup' ht id) :=
    fun a ha ↦ ⟨ha.1, ha.2.trans hxy.le⟩
  obtain ⟨a, ha, hax⟩ : ∃ a ∈ t, ¬ a ≤ x := by
    by_contra! hno
    exact hxy.not_ge (Finset.sup'_le ht id hno)
  rw [atomCount_eq_ncard, atomCount_eq_ncard]
  exact Set.ncard_lt_ncard ((Set.ssubset_iff_of_subset hsub).2
    ⟨a, ⟨hP (hPt a ha), Finset.le_sup' id ha⟩, fun h ↦ hax h.2⟩) (Set.toFinite _)

/-- The sums of `P`-atoms with `n` atoms form an antichain, so *two cats* is quantized
([champollion-krifka-2016]). -/
theorem qua_algClosure_atomCount [SemilatticeSup α] [Fintype α] {P : α → Prop}
    (hP : ∀ ⦃a⦄, P a → Atom a) (n : ℕ) : QUA fun x ↦ AlgClosure P x ∧ atomCount α x = n :=
  qua_and_eq_of_strictMonoOn (atomCount_strictMonoOn hP) n

section ExtensiveMeasure

variable {M : Type*} [SemilatticeSup α] [AddCommMonoid M] [PartialOrder M]

/-- An extensive measure function ([krifka-1989], [krifka-1998]) is additive over
non-overlapping elements and positive on non-null ones. -/
class IsExtensiveMeasure (μ : α → M) : Prop where
  additive : ∀ x y, ¬ Overlap x y → μ (x ⊔ y) = μ x + μ y
  positive : ∀ x, ¬ IsBot x → 0 < μ x

/-- Over a carrier with remainders, an extensive measure gives a proper part a smaller measure
than the whole, which adds a non-null remainder to it. -/
theorem IsExtensiveMeasure.strictMono [HasRemainders α] [AddLeftStrictMono M] (μ : α → M)
    [h : IsExtensiveMeasure μ] : StrictMono μ := fun x y hxy ↦ by
  obtain ⟨z, hz, rfl⟩ := HasRemainders.exists_remainder hxy
  rw [h.additive x z fun ho ↦ hz ho.symm]
  exact lt_add_of_pos_right _ (h.positive z fun hb ↦ hxy.ne (sup_eq_left.2 (hb x)).symm)

end ExtensiveMeasure

instance [DecidableEq β] : IsExtensiveMeasure (Finset.card : Finset β → ℕ) where
  additive _ _ h :=
    Finset.card_union_of_disjoint (not_not.mp (overlap_iff_not_disjoint.not.mp h))
  positive _ hx := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 (mt isBot_iff_eq_bot.2 hx))

end Mereology
