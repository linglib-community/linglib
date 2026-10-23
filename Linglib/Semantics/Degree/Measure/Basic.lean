module

public import Mathlib.Basic.Real.Basic
public import Linglib.Core.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith

/-!
# Admissible measures and dimensional restriction

A measure function is admissible for a background ordering when it is strictly monotone, mathlib's
`StrictMono`. The condition recurs under several names: Schwarzschild's Monotonicity Constraint on
the measures of pseudopartitives, Wellwood's admissibility for the measure of *much*, the
confidence orderings of Cariani, Santorio and Wellwood, and Pasternak's monotonicity of intensity
on mental states; Krifka's extensive measures have it over parts with remainders. A domain is
dimensionally restricted if any two admissible measures order its elements alike. Linear orders
are dimensionally restricted, and multi-dimensional orders such as weight × volume are not.

## Main definitions

* `DimensionallyRestricted`: any two admissible measures agree on the comparative ordering.

## Main statements

* `linearOrder_dimensionallyRestricted`, `prod_not_dimensionallyRestricted`: linear orders are
  dimensionally restricted, and a product order is not.

## References

* [schwarzschild-2002], [schwarzschild-2006], [krifka-1989], [wellwood-2015],
  [cariani-santorio-wellwood-2024], [pasternak-2019]
-/

@[expose] public section

namespace Degree

/-! ### Dimensional restriction -/

/-- A domain is dimensionally restricted if any two admissible measure functions into the scale
`D` agree on the comparative ordering of all its elements, so that the background ordering alone
determines the comparative. Linear orders are dimensionally restricted
(`linearOrder_dimensionallyRestricted`), and the componentwise order on `D × D` is not
(`prod_not_dimensionallyRestricted`). -/
def DimensionallyRestricted (α : Type*) [Preorder α] (D : Type := ℝ) [Preorder D] : Prop :=
  ∀ (μ₁ μ₂ : α → D), StrictMono μ₁ → StrictMono μ₂ →
    ∀ (a b : α), μ₁ a < μ₁ b ↔ μ₂ a < μ₂ b

/-- Linear orders are dimensionally restricted, since the ambient order determines the
comparative ordering whichever admissible measure function is chosen. -/
theorem linearOrder_dimensionallyRestricted {α : Type*} [LinearOrder α] {D : Type} [Preorder D] :
    DimensionallyRestricted α D :=
  fun _ _ hμ₁ hμ₂ _ _ => hμ₁.lt_iff_lt.trans hμ₂.lt_iff_lt.symm

theorem not_restricted_of_disagreement {α : Type*} [Preorder α] {D : Type} [Preorder D]
    {μ₁ μ₂ : α → D} (hμ₁ : StrictMono μ₁) (hμ₂ : StrictMono μ₂)
    {a b : α} (h₁ : μ₁ a < μ₁ b) (h₂ : ¬ μ₂ a < μ₂ b) :
    ¬ DimensionallyRestricted α D :=
  fun hDR => h₂ ((hDR μ₁ μ₂ hμ₁ hμ₂ a b).mp h₁)

/-- The componentwise-ordered `D × D` (weight × volume) is not dimensionally restricted, since
the admissible measures `2·w + v` and `w + v` order the incomparable elements `(0, 1)` and
`(1, 0)` differently; this is the multi-dimensional signature of entity and event domains. -/
theorem prod_not_dimensionallyRestricted {D : Type} [Field D] [LinearOrder D]
    [IsStrictOrderedRing D] : ¬ DimensionallyRestricted (D × D) D := by
  have hmono : ∀ c : D, 0 < c → StrictMono (fun p : D × D => c * p.1 + p.2) := by
    intro c hc p q hpq
    rcases Prod.lt_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := mul_lt_mul_of_pos_left h1 hc
      dsimp only
      nlinarith
    · have := mul_le_mul_of_nonneg_left h1 hc.le
      dsimp only
      nlinarith
  exact not_restricted_of_disagreement (μ₁ := fun p => 2 * p.1 + p.2)
    (μ₂ := fun p => 1 * p.1 + p.2) (hmono 2 (by norm_num)) (hmono 1 (by norm_num))
    (a := (0, 1)) (b := (1, 0)) (by norm_num) (by norm_num)

end Degree
