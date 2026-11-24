module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# Place functions in a vector space

In a vector space a locative says more than which region an object is in. *Ten metres outside the
house* also says how far the object is from the house. For this, a preposition sends the region
of the ground to a set of located vectors. A *located vector* is a vector together with the point
it starts at, and it *ends* at the point the vector leads to. The object is placed at the end of
one of these vectors.

We define the order on located vectors in which `v ≤ w` if `w` starts where `v` does and is `v`
lengthened, that is, `w = s • v` for some `s ≥ 1`. A set of located vectors is closed under
lengthening if it is an upper set, and closed under shortening if it is a lower set. A measure
phrase such as *ten metres* denotes a *measure set*: a set of located vectors that contains every
located vector of the same length as one of its members.

## Main definitions

* `LocatedVector`: a vector with its start point.
* `LocatedVector.finish`: the point a located vector ends at.
* `Locative.toPlace`: the place function of a map from regions to sets of located vectors.
* `Locative.IsConservative`: every vector that a map assigns to a region starts in the region.
* `Locative.IsMeasureSet`: a set of located vectors is a measure set.
* `Locative.ModificationCondition`: a set of located vectors meets every nonempty measure set.

## Implementation notes

Points and vectors have different types, related by `AddTorsor V P`. The alternative is one type
for both, with a located vector as a pair of vectors.

## TODO

* The denotations of the prepositions, which use the boundary of a region and the shortest
  located vectors from it.
* The relation between the modification condition and closure under lengthening and shortening.

## References

* [zwarts-winter-2000]
-/

@[expose] public section

/-- A located vector is a vector together with the point it starts at. -/
structure LocatedVector (V P : Type*) where
  /-- The point the vector starts at. -/
  start : P
  /-- The vector. -/
  vec : V

namespace LocatedVector

variable {V P : Type*}

/-- The point a located vector ends at. -/
def finish [AddGroup V] [AddTorsor V P] (v : LocatedVector V P) : P := v.vec +ᵥ v.start

variable [AddCommGroup V] [Module ℝ V]

/-- A located vector is below the located vectors that lengthen it. -/
instance instPreorder : Preorder (LocatedVector V P) where
  le v w := v.start = w.start ∧ ∃ s : ℝ, 1 ≤ s ∧ w.vec = s • v.vec
  le_refl v := ⟨rfl, 1, le_rfl, (one_smul ℝ _).symm⟩
  le_trans _ _ _ := fun ⟨h₁, s, hs, hv⟩ ⟨h₂, t, ht, hw⟩ ↦
    ⟨h₁.trans h₂, t * s, one_le_mul_of_one_le_of_one_le ht hs, by rw [hw, hv, mul_smul]⟩

theorem le_def {v w : LocatedVector V P} :
    v ≤ w ↔ v.start = w.start ∧ ∃ s : ℝ, 1 ≤ s ∧ w.vec = s • v.vec :=
  Iff.rfl

/-- Two located vectors that lengthen each other are equal. -/
theorem eq_of_le_of_ge {v w : LocatedVector V P} (h : v ≤ w) (h' : w ≤ v) : v = w := by
  obtain ⟨a, x⟩ := v
  obtain ⟨b, y⟩ := w
  obtain ⟨rfl, s, hs, hy⟩ := h
  obtain ⟨-, t, ht, hx⟩ := h'
  dsimp only at hy hx
  suffices x = y by rw [this]
  have h0 : (t * s - 1) • x = 0 := by rw [sub_smul, mul_smul, ← hy, ← hx, one_smul, sub_self]
  rcases smul_eq_zero.1 h0 with h1 | h1
  · have := mul_nonneg (sub_nonneg.2 ht) (sub_nonneg.2 hs)
    obtain rfl : s = 1 := le_antisymm (by nlinarith) hs
    rw [hy, one_smul]
  · rw [hy, h1, smul_zero]

instance : PartialOrder (LocatedVector V P) where
  le_antisymm _ _ := eq_of_le_of_ge

end LocatedVector

namespace Locative

variable {V P : Type*}

/-- The place function of a map from regions to sets of located vectors: the points where the
vectors of a region end. -/
def toPlace [AddGroup V] [AddTorsor V P] (F : Set P → Set (LocatedVector V P)) (A : Set P) :
    Set P :=
  LocatedVector.finish '' F A

/-- A map from regions to sets of located vectors is *conservative* if every vector it assigns to
a region starts in the region. -/
def IsConservative (F : Set P → Set (LocatedVector V P)) : Prop :=
  ∀ ⦃A v⦄, v ∈ F A → v.start ∈ A

variable [NormedAddCommGroup V]

/-- A *measure set* contains every located vector of the same length as one of its members. -/
def IsMeasureSet (M : Set (LocatedVector V P)) : Prop :=
  ∀ ⦃v w : LocatedVector V P⦄, v ∈ M → ‖w.vec‖ = ‖v.vec‖ → w ∈ M

/-- A set of located vectors satisfies the *modification condition* if it meets every nonempty
measure set. -/
def ModificationCondition (W : Set (LocatedVector V P)) : Prop :=
  ∀ M : Set (LocatedVector V P), IsMeasureSet M → M.Nonempty → (M ∩ W).Nonempty

theorem isMeasureSet_iff {M : Set (LocatedVector V P)} :
    IsMeasureSet M ↔ ∃ S : Set ℝ, M = {v | ‖v.vec‖ ∈ S} := by
  refine ⟨fun h ↦ ⟨(fun v : LocatedVector V P ↦ ‖v.vec‖) '' M, Set.ext fun w ↦
    ⟨fun hw ↦ ⟨w, hw, rfl⟩, fun ⟨v, hv, hvw⟩ ↦ h hv hvw.symm⟩⟩, ?_⟩
  rintro ⟨S, rfl⟩ v w hv hw
  exact (congrArg (· ∈ S) hw).mpr hv

end Locative
