module

public import Linglib.Semantics.Quantification.Basic
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Closure

/-!
# Witness sets

A witness set for a type ⟨1⟩ quantifier `Q` living on `A` is a subset of `A` that `Q` holds of
(§4.9 of Barwise and Cooper). Such a quantifier holds of `X` exactly when `A ∩ X` is a witness
set. Witness sets characterise the monotone quantifiers: an increasing quantifier holds of `X`
iff `X` contains one of its witness sets, and a decreasing quantifier holds of `X` iff `X ∩ A`
is contained in one (C11). Living on `A` already confines the minimal sets in `Q` to `A`, so the
minimal witness sets are exactly the minimal sets in the quantifier: those of *some* `A` are the
singletons of its members, the upper closure of which is *some* `A`, and that of *every* `A` is `A`
itself.

## Main definitions

* `Quantifier.Witness Q A w`: `w ⊆ A` and `Q w`.

## Main statements

* `Quantifier.LivesOn.apply_iff_witness`: a quantifier living on `A` holds of `X` iff
  `A ∩ X` is a witness set.
* `Quantifier.LivesOn.monotone_apply_iff`, `Quantifier.LivesOn.antitone_apply_iff`: C11
  for increasing and decreasing quantifiers.
* `Quantifier.LivesOn.minimal_witness_iff`: the minimal witness sets of a quantifier living
  on `A` are its minimal sets.
* `Quantifier.Det.minimal_some_iff`, `Quantifier.Det.minimal_every_iff`: the minimal sets of
  *some* and *every*.

## References

* [barwise-cooper-1981]
-/

@[expose] public section

namespace Quantifier

variable {α : Type*} {Q : Quantifier α} {A X w : Set α}

/-- A witness set for a quantifier living on `A` is a subset of `A` in the quantifier
([barwise-cooper-1981] §4.9). -/
def Witness (Q : Quantifier α) (A w : Set α) : Prop := w ⊆ A ∧ Q w

/-- A quantifier living on `A` holds of `X` iff `A ∩ X` is a witness set, whatever its
monotonicity. -/
theorem LivesOn.apply_iff_witness (h : Q.LivesOn A) : Q X ↔ Q.Witness A (A ∩ X) :=
  ⟨fun hX ↦ ⟨Set.inter_subset_left, (h X).1 hX⟩, fun hw ↦ (h X).2 hw.2⟩

/-- C11(i) says that an increasing quantifier living on `A` holds of `X` iff some witness set
is contained in `X`. -/
theorem LivesOn.monotone_apply_iff (h : Q.LivesOn A) (hm : Monotone Q) :
    Q X ↔ ∃ w, Q.Witness A w ∧ w ⊆ X :=
  ⟨fun hX ↦ ⟨_, h.apply_iff_witness.1 hX, Set.inter_subset_right⟩,
    fun ⟨_, hw, hwX⟩ ↦ hm hwX hw.2⟩

/-- C11(ii) says that a decreasing quantifier living on `A` holds of `X` iff `X ∩ A` is
contained in some witness set. -/
theorem LivesOn.antitone_apply_iff (h : Q.LivesOn A) (hm : Antitone Q) :
    Q X ↔ ∃ w, Q.Witness A w ∧ X ∩ A ⊆ w :=
  ⟨fun hX ↦ ⟨_, h.apply_iff_witness.1 hX, (Set.inter_comm X A).le⟩,
    fun ⟨_, hw, hXw⟩ ↦ (h X).2 (hm ((Set.inter_comm A X).le.trans hXw) hw.2)⟩

/-- The minimal witness sets of a quantifier living on `A` are its minimal sets, since a
minimal set in `Q` lies inside `A`, `Q` holding also of its intersection with `A`. -/
theorem LivesOn.minimal_witness_iff (h : Q.LivesOn A) :
    Minimal (Q.Witness A) w ↔ Minimal Q w :=
  ⟨fun hm ↦ ⟨hm.1.2, fun _ hy hyw ↦ hm.2 ⟨hyw.trans hm.1.1, hy⟩ hyw⟩,
    fun hm ↦
      have hle : w ⊆ A ∩ w := hm.2 ((h w).1 hm.1) Set.inter_subset_right
      ⟨⟨hle.trans Set.inter_subset_left, hm.1⟩, fun _ hy hyw ↦ hm.2 hy.2 hyw⟩⟩

/-! ### *Some* and *every* -/

/-- *Some* `A` holds of the upper closure of the singletons of `A`. -/
theorem Det.setOf_some_eq_upperClosure (A : Set α) :
    {B | Det.some A B} = upperClosure ((fun x ↦ ({x} : Set α)) '' A) := by
  ext B; simp [Det.some, Set.Nonempty]

/-- The minimal sets in *some* `A` are the singletons of its members. -/
theorem Det.minimal_some_iff : Minimal (Det.some A) w ↔ ∃ x ∈ A, w = {x} := by
  refine ⟨fun ⟨⟨x, hxA, hxw⟩, hmin⟩ ↦ ⟨x, hxA, ?_⟩, ?_⟩
  · exact (hmin (y := {x}) ⟨x, hxA, rfl⟩ (Set.singleton_subset_iff.2 hxw)).antisymm
      (Set.singleton_subset_iff.2 hxw)
  · rintro ⟨x, hxA, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, fun v ⟨y, _, hyv⟩ hvx ↦ ?_⟩
    obtain rfl : y = x := hvx hyv
    exact Set.singleton_subset_iff.2 hyv

/-- The minimal set in *every* `A` is `A`. -/
theorem Det.minimal_every_iff : Minimal (Det.every A) w ↔ w = A :=
  minimal_ge_iff

end Quantifier
