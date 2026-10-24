module

public import Mathlib.Data.Fintype.EquivFin

/-!
# Polarity

This file defines polarity, the syncretism of a form over two features in which two cells share
a form exactly when they differ in both features or in neither, so that each cell's form is that
of its polar opposite.

Polarity is the morphological exchange of the Somali article, whose form for one gender in one
number is its form for the other gender in the other number, not the polarity of a clause. A
polar form separates the values of each feature at every value of the other, and it confines
both features to two values.

## Main definitions

* `Morphology.Polar`: a form over two features is polar.

## Main results

* `Morphology.Polar.injective`: a polar form separates the values of the first feature at every
  value of the second.
* `Morphology.Polar.card_le_two`, `Morphology.Polar.card_eq_two`: polarity confines either
  feature to two values.

## References

* [corbett-1991] — chapter 7
* [corbett-1998]
-/

@[expose] public section

namespace Morphology

variable {G T F : Type*}

/-- A form over two features is polar when two cells share a form exactly when they differ in
both features or in neither. -/
def Polar (f : G → T → F) : Prop :=
  ∀ g g' t t', f g t = f g' t' ↔ (g = g' ↔ t = t')

variable {f : G → T → F}

instance [Fintype G] [Fintype T] [DecidableEq G] [DecidableEq T] [DecidableEq F] :
    Decidable (Polar f) := by
  unfold Polar; infer_instance

theorem Polar.flip (h : Polar f) : Polar (flip f) :=
  fun t t' g g' ↦ (h g g' t t').trans Iff.comm

theorem Polar.injective (h : Polar f) (t : T) : Function.Injective (f · t) :=
  fun _ _ e ↦ ((h _ _ t t).mp e).mpr rfl

/-- A polar form admits at most two values of either feature, since with three values of one
feature two of them would share a form. -/
theorem Polar.card_le_two [Fintype G] [Nontrivial T] (h : Polar f) : Fintype.card G ≤ 2 := by
  by_contra hc
  obtain ⟨g₁, g₂, g₃, h₁₂, h₁₃, h₂₃⟩ := Fintype.two_lt_card_iff.mp (not_le.mp hc)
  obtain ⟨t, t', ht⟩ := exists_pair_ne T
  have e₁ : f g₁ t = f g₂ t' := (h g₁ g₂ t t').mpr (iff_of_false h₁₂ ht)
  have e₃ : f g₃ t = f g₂ t' := (h g₃ g₂ t t').mpr (iff_of_false h₂₃.symm ht)
  exact h₁₃ (h.injective t (e₁.trans e₃.symm))

theorem Polar.card_eq_two [Fintype G] [Nontrivial G] [Nontrivial T] (h : Polar f) :
    Fintype.card G = 2 :=
  le_antisymm h.card_le_two Fintype.one_lt_card

end Morphology
