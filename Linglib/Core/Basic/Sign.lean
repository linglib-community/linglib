module

public import Mathlib.Algebra.Notation.Support
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Opposite signs and sign vectors

When two elements have opposite signs, and when two differences from a common point do: exactly
when the point lies strictly between the two elements, or all three coincide. A sign vector
`v : α → SignType` splits its nonzero entries into its positive and negative supports.

## Main definitions

* `posSupport v`, `negSupport v`: where the sign vector `v` is `1`, and where it is `-1`.

## Main results

* `sign_eq_neg_sign_iff`: two elements have opposite signs when they lie strictly on opposite
  sides of zero or both vanish.
* `sign_sub_eq_neg_sign_sub_iff`: `a - c` and `b - c` have opposite signs when `c` lies strictly
  between `a` and `b`, or `a = b = c`.
* `posSupport_union_negSupport`: together the two supports are `Function.support v`.
-/

@[expose] public section

variable {α : Type*}

theorem sign_eq_neg_sign_iff [Zero α] [LinearOrder α] {x y : α} :
    SignType.sign x = -SignType.sign y ↔ x < 0 ∧ 0 < y ∨ 0 < x ∧ y < 0 ∨ x = 0 ∧ y = 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx <;> rcases lt_trichotomy y 0 with hy | rfl | hy <;>
    simp_all [sign_neg, sign_pos, lt_asymm, ne_of_lt, ne_of_gt]

theorem sign_sub_eq_neg_sign_sub_iff [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
    {a b c : α} :
    SignType.sign (a - c) = -SignType.sign (b - c) ↔ c ∈ Set.uIoo a b ∨ a = c ∧ b = c := by
  rw [sign_eq_neg_sign_iff]
  simp only [Set.uIoo, Set.mem_Ioo, inf_lt_iff, lt_sup_iff, sub_neg, sub_pos, sub_eq_zero]
  grind

/-! ### Supports of a sign vector -/

section Support

variable {v : α → SignType} {a : α}

/-- The positive support of a sign vector is where it is `1`. -/
def posSupport (v : α → SignType) : Set α := {a | v a = 1}

/-- The negative support of a sign vector is where it is `-1`. -/
def negSupport (v : α → SignType) : Set α := {a | v a = -1}

@[simp] theorem mem_posSupport : a ∈ posSupport v ↔ v a = 1 := Iff.rfl

@[simp] theorem mem_negSupport : a ∈ negSupport v ↔ v a = -1 := Iff.rfl

instance (v : α → SignType) : DecidablePred (· ∈ posSupport v) :=
  fun a ↦ inferInstanceAs (Decidable (v a = 1))

instance (v : α → SignType) : DecidablePred (· ∈ negSupport v) :=
  fun a ↦ inferInstanceAs (Decidable (v a = -1))

@[simp] theorem posSupport_neg (v : α → SignType) : posSupport (-v) = negSupport v :=
  Set.ext fun a ↦ by simp [neg_eq_iff_eq_neg]

@[simp] theorem negSupport_neg (v : α → SignType) : negSupport (-v) = posSupport v :=
  Set.ext fun a ↦ by simp [neg_eq_iff_eq_neg]

theorem disjoint_posSupport_negSupport (v : α → SignType) :
    Disjoint (posSupport v) (negSupport v) :=
  Set.disjoint_left.mpr fun a h₁ h₂ ↦
    absurd ((mem_posSupport.mp h₁).symm.trans (mem_negSupport.mp h₂)) (by decide)

theorem posSupport_union_negSupport (v : α → SignType) :
    posSupport v ∪ negSupport v = Function.support v := by
  ext a; cases h : v a <;> simp [h]

theorem posSupport_subset_support (v : α → SignType) : posSupport v ⊆ Function.support v :=
  fun a (h : v a = 1) ↦ by simp [Function.mem_support, h]

theorem negSupport_subset_support (v : α → SignType) : negSupport v ⊆ Function.support v :=
  fun a (h : v a = -1) ↦ by simp [Function.mem_support, h]

theorem support_inter_compl_posSupport (v : α → SignType) :
    Function.support v ∩ (posSupport v)ᶜ = negSupport v := by
  ext a; cases h : v a <;> simp [h]

end Support
