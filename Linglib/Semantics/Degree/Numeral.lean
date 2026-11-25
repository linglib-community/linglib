/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Denotation
public import Linglib.Core.Order.Cover
public import Linglib.Semantics.Exhaustification.Basic
public import Linglib.Semantics.Quantifier.Predicative

/-!
# Numeral meanings

A bare numeral and its modified forms *more than*, *fewer than*, *at least* and *at most* are the
five comparisons of `Comparison`. On the de-Fregean semantics of [kennedy-2015], the form with
comparison `c` and number `m` is the degree quantifier `MaxIn (c.interval m)`, so the bare numeral
`MaxIn {m}` is two-sided. In the tradition of [horn-1972] the bare numeral is the lower-bounded
`individual m`. This file derives each reading from the other, by type shifting and by
exhaustification, and defines the numeral modifiers as lexical items.

## Main results

* `Numerals.BE_maxIn`: `BE (MaxIn U) = U`.
* `Numerals.maxIn_singleton_lt_individual`: on a scale with no greatest degree, the two-sided
  numeral strictly entails the lower-bounded one.
* `Numerals.isGreatest_ge_iff`: exhaustified against the higher numerals, *at least `m`* holds of
  `a` if and only if `a = m`.
* `Numerals.mem_exh_range_interval_gt_iff`: exhaustified against its forms at the other numbers,
  *more than `m`* holds of `a` if and only if `a` covers `m`.

## Implementation notes

A Class A modifier relates the numeral to a definite amount, so *a hexagon has fewer than 11 sides*
is a weak truth. A Class B modifier places a bound on a range of amounts, so *a hexagon has at most
10 sides* is odd, and the modifier conveys that the speaker does not know the amount. [kennedy-2015]
and [rett-2015a] reduce the two classes to the ordering the modifier expresses, exclusive for Class
A and inclusive for Class B, and derive the ignorance as an implicature.
[schwarz-buccola-hamilton-2012] show that *at most* and *up to* dissociate,
[cremers-coppock-dotlacil-roelofsen-2022] find the ignorance contrast graded and dependent on the
question under discussion, and [enguehard-2018] derives the inferences of comparative numerals from
granularity.

The class of each kind follows the classification of the English modifiers in [nouwen-2010]. The
comparatives are Class A, and the superlatives and the adverbs are Class B. A prepositional modifier
follows its spatial use: a locative preposition gives a Class A modifier and a directional one a
Class B modifier. *Over* is Class A although its usual spatial sense is directional.

## References

* [kennedy-2015]
* [horn-1972]
* [partee-1987]
* [spector-2013]
* [chierchia-fox-spector-2012]
* [nouwen-2010]
* [rett-2015a]
* [schwarz-buccola-hamilton-2012]
* [cremers-coppock-dotlacil-roelofsen-2022]
* [enguehard-2018]
-/

@[expose] public section

namespace Numerals

open Exhaustification Quantifier

/-! ### The two readings of a bare numeral -/

section Readings

variable {D : Type*}

/-- `BE` takes the de-Fregean form with interval `U` to the property of lying in `U`
([kennedy-2015], (39)). -/
theorem BE_maxIn [Preorder D] (U : Set D) : Quantifier.BE (MaxIn U) = U :=
  Set.ext fun x ↦
    ⟨fun ⟨_, hm, h⟩ ↦ (h.1 : _ = x) ▸ hm, fun hx ↦ ⟨x, hx, isGreatest_singleton⟩⟩

/-- Existential closure over the lowered bare numeral is the individual of the number, the
lower-bounded reading ([kennedy-2015], (40b) and fn. 3). -/
theorem some_BE_maxIn_singleton [Preorder D] (m : D) :
    Det.some (Quantifier.BE (MaxIn {m})) = Quantifier.individual m := by
  rw [BE_maxIn]
  exact Quantifier.some_singleton m

/-- On a scale without a top degree the two-sided bare numeral asymmetrically entails the
lower-bounded one. -/
theorem maxIn_singleton_lt_individual [Preorder D] [NoMaxOrder D] (m : D) :
    MaxIn {m} < Quantifier.individual m :=
  lt_of_le_not_ge (fun _ h ↦ (maxIn_singleton.1 h).1) fun h ↦
    let ⟨a, ha⟩ := exists_gt m
    ha.not_ge ((maxIn_singleton.1 (h (Set.Iic a) ha.le)).2 le_rfl)

/-- Exhaustified against the higher numerals, *at least `m`* is true of `a` if and only if `a` is
`m`. -/
theorem isGreatest_ge_iff [PartialOrder D] {a m : D} :
    IsGreatest {j | a ∈ Comparison.ge.interval j} m ↔ a ∈ Comparison.eq.interval m :=
  ⟨fun h ↦ le_antisymm (h.2 (le_refl a)) h.1, by rintro rfl; exact ⟨le_rfl, fun _ h ↦ h⟩⟩

end Readings

/-! ### Exhaustification on the scale of numerals

The scalar alternatives of a numeral form are the same form at the other numbers, and
exhaustifying the form denies those it does not entail. A form that keeps its number comes out
exact, and one that excludes it comes out true only of the amount next to the number, which a
dense scale does not have. -/

section Scale

variable {D : Type*} {a m : D}

variable [LinearOrder D]

/-- Exhaustified against its forms at the other numbers, a form that keeps its number, the bare
numeral, *at least* or *at most*, is true only of that number. -/
theorem mem_exh_range_interval_iff_of_not_isStrict {c : Comparison} (hc : ¬ c.IsStrict) :
    a ∈ exh (Set.range c.interval) (c.interval m) ↔ a = m := by
  rw [mem_exh_range_iff]
  cases c
  · simp only [Comparison.interval_eq, Set.singleton_subset_singleton, Set.mem_singleton_iff]
    exact ⟨And.left, fun h ↦ ⟨h, fun _ hi ↦ h.symm.trans hi⟩⟩
  · simp only [Comparison.interval_ge, Set.Ici_subset_Ici]
    exact isGreatest_ge_iff
  · exact absurd trivial hc
  · simp only [Comparison.interval_le, Set.Iic_subset_Iic, Set.mem_Iic]
    exact ⟨fun h ↦ le_antisymm h.1 (h.2 a le_rfl), by rintro rfl; exact ⟨le_rfl, fun _ h ↦ h⟩⟩
  · exact absurd trivial hc

/-- Exhaustified against its forms at the other numbers, *more than `m`* is true of `a` exactly
when `a` covers `m`. -/
theorem mem_exh_range_interval_gt_iff :
    a ∈ exh (Set.range Comparison.gt.interval) (Comparison.gt.interval m) ↔ m ⋖ a := by
  rw [mem_exh_range_iff]
  simp only [Comparison.interval_gt, Set.Ioi_subset_Ioi_iff]
  exact isGreatest_Iio_iff_covBy

/-- Exhaustified against its forms at the other numbers, *fewer than `m`* is true of `a` exactly
when `m` covers `a`. -/
theorem mem_exh_range_interval_lt_iff :
    a ∈ exh (Set.range Comparison.lt.interval) (Comparison.lt.interval m) ↔ a ⋖ m := by
  rw [mem_exh_range_iff]
  simp only [Comparison.interval_lt, Set.Iio_subset_Iio_iff]
  exact isLeast_Ioi_iff_covBy

end Scale

/-! ### Numeral modifiers -/

/-- The two classes of numeral modifiers of [nouwen-2010]: a Class A modifier relates the numeral to
a definite amount, and a Class B modifier places a bound on a range of amounts. -/
inductive ModifierClass where
  | classA
  | classB
  deriving Repr, DecidableEq

/-- The constructions a numeral modifier taking a single numeral is built on, in [nouwen-2010]'s
classification. The disjunctive *n or more* and the two-numeral *between* and *from … to* are left
out. -/
inductive ModifierKind where
  /-- A comparative, such as *more than* or *fewer than*. -/
  | comparative
  /-- A superlative, such as *at least* or *at most*. -/
  | superlative
  /-- A locative preposition, such as *over* or *under*. -/
  | locative
  /-- A directional preposition, such as *up to* or *from*. -/
  | directional
  /-- An adverb of minimality or maximality, such as *minimally* or *maximally*. -/
  | adverbial
  /-- An equative, such as *as many as*, which [rett-2015a] adds to Class B. -/
  | equative
  deriving Repr, DecidableEq

/-- The class of each kind, after the classification of the English modifiers in [nouwen-2010]. -/
def ModifierKind.modifierClass : ModifierKind → ModifierClass
  | .comparative | .locative => .classA
  | .superlative | .directional | .adverbial | .equative => .classB

/-- A numeral modifier, an expression that combines with a numeral to bound, fix or approximate
the amount it names. -/
structure NumeralModifier where
  /-- The surface form. -/
  form : String
  /-- The construction the modifier is built on, `none` for the exactifiers and approximators,
  which [nouwen-2010]'s classification does not cover. -/
  kind : Option ModifierKind
  /-- The readings the literature makes available, each a modifier of sets of amounts that sends
  the bare numeral's two-sided meaning `{n}` to the amounts verifying the modified numeral. -/
  readings : Set (Modifier (Set ℕ))

namespace NumeralModifier

/-- A numeral modifier denotes its readings. -/
instance : Denotes NumeralModifier (Set (Modifier (Set ℕ))) := ⟨readings⟩

open scoped Denotes in
@[simp] theorem denote_eq_readings (w : NumeralModifier) : ⟦w⟧ = w.readings := rfl

/-- The class of a bound-setting modifier, read off its kind. -/
def modifierClass (w : NumeralModifier) : Option ModifierClass := w.kind.map (·.modifierClass)

/-- The numeral modifier with the one reading of a comparison, as a bound-setting modifier or an
exactifier has. -/
def ofComparison (form : String) (kind : Option ModifierKind) (c : Comparison) : NumeralModifier :=
  ⟨form, kind, {c.modifier}⟩

variable {form : String} {kind : Option ModifierKind} {c : Comparison}

@[simp] theorem kind_ofComparison : (ofComparison form kind c).kind = kind := rfl

@[simp] theorem readings_ofComparison : (ofComparison form kind c).readings = {c.modifier} := rfl

end NumeralModifier

end Numerals
