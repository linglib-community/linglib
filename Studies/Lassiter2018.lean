/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Lassiter (2018): Complex Sentential Operators Refute Unrestricted Simplification

Simplification of disjunctive antecedents takes *if φ or ψ, χ* to *if φ, χ* and *if ψ, χ*.
The paper's examples have a consequent that bounds a probability from both sides. Jim is
indifferent among the odd numbers, and *if Jim had bet on 1 or 3, there is an exactly 50%
probability that he would have bet on 3* is acceptable, while its two simplifications are not
satisfiable: after a bet on 1 the probability of a bet on 3 is zero, and after a bet on 3 it is
one (`dirac_three`). Under the even mixture of the two bets it is one half (`indifferent_three`).

## Implementation notes

The paper gives judgments and no semantics for the conditional. The even mixture `indifferent`
is one way of making the acceptable sentence true: it takes Jim's indifference among the odd
numbers to carry over to the two bets of the antecedent. The paper's other examples, with
*likely but not certain* and *usually but not always*, are not formalized.

## References

* [lassiter-2018]
-/

@[expose] public section

namespace Lassiter2018

open MeasureTheory
open scoped ENNReal

/-- The odd numbers Jim might bet on. -/
inductive Bet | one | three | five
  deriving DecidableEq

instance : MeasurableSpace Bet := ⊤
instance : MeasurableSingletonClass Bet := ⟨fun _ ↦ trivial⟩

/-- The even mixture of a bet on 1 and a bet on 3. -/
noncomputable def indifferent : Measure Bet :=
  (2⁻¹ : ℝ≥0∞) • Measure.dirac Bet.one + (2⁻¹ : ℝ≥0∞) • Measure.dirac Bet.three

/-- (10): under the even mixture of the two bets the probability of a bet on 3 is exactly one
half. -/
theorem indifferent_three : indifferent {Bet.three} = 2⁻¹ := by
  simp [indifferent]

/-- (10a), (10b): after either single bet the probability of a bet on 3 is zero or one, so
neither simplification of (10) can be true. -/
theorem dirac_three (b : Bet) :
    Measure.dirac b ({Bet.three} : Set Bet) = 0 ∨ Measure.dirac b ({Bet.three} : Set Bet) = 1 := by
  cases b <;> simp

end Lassiter2018
