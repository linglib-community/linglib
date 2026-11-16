module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Order.Ring.Defs
public import Linglib.Core.Algebra.Order.Group.Action.End

/-!
# Invariance under changes of scale

A change of scale acts on the degrees, and so on every measure. A function of measures is
[invariant](##Invariant) under a set of changes of scale when none of them changes its value, and
a statement invariant under the changes of a scale is meaningful on it. [Comparing two
measures](##invariant_univ_lt) is invariant under every strictly increasing change of scale, the
changes of an ordinal scale; the changes of an interval scale are the [positive affine
maps](##positiveAffine) and those of a ratio scale the [similarities](##similarity).

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

variable {G D E β K F : Type*}

/-- A function of measures is invariant under a set of changes of scale when none of them changes
its value. -/
def Invariant [SMul G D] (S : Set G) (a : (E → D) → β) : Prop :=
  ∀ g ∈ S, ∀ μ, a (g • μ) = a μ

theorem Invariant.mono [SMul G D] {S T : Set G} (h : S ⊆ T) {a : (E → D) → β}
    (ha : Invariant T a) : Invariant S a :=
  fun g hg ↦ ha g (h hg)

/-- Comparing two measures is invariant under every strictly increasing change of scale. -/
theorem invariant_univ_lt [LinearOrder D] (x y : E) :
    Invariant (univ : Set (D ↪o D)) fun μ : E → D ↦ μ y < μ x :=
  fun g _ _ ↦ propext g.lt_iff_lt

section Semiring

variable [Semiring K] [PartialOrder K] [FunLike F K K]

/-- The positive affine maps `t ↦ a * t + b` with `0 < a`, the changes of scale of an interval
scale. -/
def positiveAffine : Set F := {g | ∃ a : K, 0 < a ∧ ∃ b : K, ∀ t, g t = a * t + b}

/-- The similarities `t ↦ a * t` with `0 < a`, the changes of scale of a ratio scale. -/
def similarity : Set F := {g | ∃ a : K, 0 < a ∧ ∀ t, g t = a * t}

theorem similarity_subset_positiveAffine : (similarity : Set F) ⊆ positiveAffine :=
  fun _ ⟨a, ha, hg⟩ ↦ ⟨a, ha, 0, fun t ↦ by rw [hg, add_zero]⟩

end Semiring
