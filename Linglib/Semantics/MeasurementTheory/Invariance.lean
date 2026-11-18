module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Group.Action.End

/-!
# Invariance under changes of scale

A change of scale acts on the degrees, and so on every measure. A function of measures is
[invariant](##MeasurementTheory.Invariant) under a set of changes of scale when none of them changes
its value, and a statement invariant under the changes of a scale is meaningful on it. The changes
of an ordinal scale are the strictly increasing maps, those of an interval scale the [positive
affine maps](##MeasurementTheory.positiveAffine), and those of a ratio scale, whose degrees are
positive, the [similarities](##MeasurementTheory.similarity). These are the maps relating any two
measures of an order, of the differences of a torsor, and of an ordered group, as `Scale`,
`Difference` and `Extensive` show.

## Implementation notes

The changes of scale are elements of a type acting on the degrees, such as the order embeddings
`D ↪o D`, so that a vector of changes of scale acts on a vector of degrees coordinatewise.
`positiveAffine` and `similarity` are sets in any type of maps of an ordered semiring, so that the
same definition serves order embeddings and order automorphisms.

## References

* [stevens-1946]
* [luce-krantz-suppes-tversky-1990]
-/

@[expose] public section

open Set

namespace MeasurementTheory

variable {G D E β K F : Type*}

/-- A function of measures is invariant under a set of changes of scale when none of them changes
its value: invariance under the permissible transformations of a scale. -/
-- [luce-krantz-suppes-tversky-1990] section 22.3.1
def Invariant [SMul G D] (S : Set G) (a : (E → D) → β) : Prop :=
  ∀ g ∈ S, ∀ μ, a (g • μ) = a μ

theorem Invariant.mono [SMul G D] {S T : Set G} (h : S ⊆ T) {a : (E → D) → β}
    (ha : Invariant T a) : Invariant S a :=
  fun g hg ↦ ha g (h hg)

section Semiring

variable [Semiring K] [PartialOrder K] [FunLike F K K]

/-- The positive affine maps `t ↦ a * t + b` with `0 < a`, the changes of scale of an interval
scale. -/
def positiveAffine : Set F := {g | ∃ a : K, 0 < a ∧ ∃ b : K, ∀ t, g t = a * t + b}

/-- The similarities `t ↦ a * t` with `0 < a`, the changes of unit of a scale with a zero; on
positive degrees they are the changes of scale of a ratio scale. -/
def similarity : Set F := {g | ∃ a : K, 0 < a ∧ ∀ t, g t = a * t}

theorem similarity_subset_positiveAffine : (similarity : Set F) ⊆ positiveAffine :=
  fun _ ⟨a, ha, hg⟩ ↦ ⟨a, ha, 0, fun t ↦ by rw [hg, add_zero]⟩

end Semiring

end MeasurementTheory
