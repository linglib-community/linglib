module

public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Place functions

A locative such as *inside the house* picks out a region of space from the region the house
occupies. A *place function* is a map `f : Set P → Set P` that sends the region of the ground to
the region of the locative. For example, *inside* is the identity and *outside* is the
complement.

The inferences a locative supports are order properties of its place function. *Inside* is
monotone: the house is in Paris, Paris is in France, so the house is in France. *Outside* is
antitone. We write these as `MonotoneOn f X` and `AntitoneOn f X` for a family `X` of regions. A
weaker property holds of place functions that are neither. We say that `f` is *point continuous*
on `X` if `f A ∩ f C ⊆ f B` for all `A ⊆ B ⊆ C` in `X`.

## Main definitions

* `Locative.PointContinuousOn`: a place function is point continuous on a family of regions.

## Main results

* `MonotoneOn.pointContinuousOn`, `AntitoneOn.pointContinuousOn`: a monotone or antitone place
  function is point continuous.
* `Locative.pointContinuousOn_univ_iff`: a place function is point continuous on all regions if
  and only if, for every point, the regions it sends to a region containing the point form an
  order-connected set.

## TODO

* The place function of each value of `Locative.Configuration`.
* The regions that entities occupy: closed, convex, nonempty and proper.

## References

* [zwarts-winter-2000]
-/

@[expose] public section

namespace Locative

variable {P : Type*} {f : Set P → Set P} {X : Set (Set P)}

/-- A place function is *point continuous* on a family of regions if a point that it places
relative to two regions of the family is placed relative to every region of the family between
them. -/
def PointContinuousOn (f : Set P → Set P) (X : Set (Set P)) : Prop :=
  ∀ ⦃A⦄, A ∈ X → ∀ ⦃B⦄, B ∈ X → ∀ ⦃C⦄, C ∈ X → A ⊆ B → B ⊆ C → f A ∩ f C ⊆ f B

theorem _root_.MonotoneOn.pointContinuousOn (hf : MonotoneOn f X) : PointContinuousOn f X :=
  fun _ hA _ hB _ _ hAB _ _ hp ↦ hf hA hB hAB hp.1

theorem _root_.AntitoneOn.pointContinuousOn (hf : AntitoneOn f X) : PointContinuousOn f X :=
  fun _ _ _ hB _ hC _ hBC _ hp ↦ hf hB hC hBC hp.2

theorem PointContinuousOn.mono {Y : Set (Set P)} (hf : PointContinuousOn f X) (h : Y ⊆ X) :
    PointContinuousOn f Y :=
  fun _ hA _ hB _ hC ↦ hf (h hA) (h hB) (h hC)

theorem pointContinuousOn_univ_iff :
    PointContinuousOn f Set.univ ↔ ∀ p, {A | p ∈ f A}.OrdConnected :=
  ⟨fun h _ ↦ ⟨fun _ hA _ hC _ hB ↦ h trivial trivial trivial hB.1 hB.2 ⟨hA, hC⟩⟩,
    fun h _ _ _ _ _ _ hAB hBC p hp ↦ (h p).out hp.1 hp.2 ⟨hAB, hBC⟩⟩

end Locative
