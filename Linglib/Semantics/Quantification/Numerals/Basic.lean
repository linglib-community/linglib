/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Comparison
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Exhaustification.Pointwise

/-!
# Numeral meanings

This file collects what is specific to numerals over the degree comparisons of
`Semantics/Degree/Comparison.lean`. A bare numeral and its four modifications, *more than*,
*fewer than*, *at least* and *at most*, are the five comparisons of `Degree.Comparison`: in
Kennedy's de-Fregean semantics the form with relation `REL` and number `m` is true of a degree
property whose greatest degree stands in `REL` to `m`. On counts the form denotes the interval
`c.interval m`, and on worlds measured by `μ` the set `μ ⁻¹' c.interval m`, so the forms have no
names of their own here. The meanings of the modified forms are common ground. Accounts differ on
the bare numeral, which has the two-sided meaning `Comparison.eq.interval m` for Kennedy and the
lower-bounded meaning `Comparison.ge.interval m` in the tradition of Horn, each account deriving the
other reading. Exhaustifying the lower-bounded meaning against the scale of higher numerals gives
the two-sided one, and Kennedy's type lowering, existential closure over the two-sided meaning at
the degrees above, takes it to the lower-bounded one.

## Main definitions

* `Numerals.ModifierClass`, `Numerals.ModifierKind`: Nouwen's two classes of numeral modifier
  and the constructions modifiers are built on, with `ModifierKind.modifierClass`.
* `Numerals.NumeralModifier`: a numeral modifier as a lexical item, its form, kind and
  readings, each reading a `Modifier (Set ℕ)` of sets of amounts.
* `Numerals.exhNumeral`: the lower-bounded meaning exhaustified against the next numeral.

## Main results

* `Numerals.exhNumeral_eq`: the exhaustified lower-bounded meaning is the two-sided one.
* `Numerals.mem_exhNumeral_iff_exhAgainst`: exhaustifying against the next numeral is
  exhaustifying against the whole scale.

## References

* [C. Kennedy, *A "de-Fregean" semantics (and neo-Gricean pragmatics) for modified and
  unmodified numerals* (2015)][kennedy-2015]
* [R. Nouwen, *Two kinds of modified numerals* (2010)][nouwen-2010]
* [L. R. Horn, *On the Semantic Properties of Logical Operators in English* (1972)][horn-1972]
* [B. Spector, *Bare numerals and scalar implicatures* (2013)][spector-2013]
* [G. Chierchia, D. Fox and B. Spector, *Scalar Implicature as a Grammatical Phenomenon*
  (2012)][chierchia-fox-spector-2012]
-/

@[expose] public section

namespace Numerals

open Degree

/-! ### Numeral modifiers -/

/-- The two classes of numeral modifiers of [nouwen-2010]. A Class A modifier relates the
numeral to a definite amount, so *a hexagon has fewer than 11 sides* is a weak truth. A Class B
modifier places a bound on a range of amounts, so *a hexagon has at most 10 sides* is odd and
the modifier conveys that the speaker does not know the amount.

[kennedy-2015] reduces the split to the ordering the modifier expresses, exclusive for Class A
and inclusive for Class B (`Degree.Comparison.boundary_mem`), and derives the ignorance as an
implicature. The categorical pattern is contested, since [schwarz-buccola-hamilton-2012] show
that *at most* and *up to* dissociate, [cremers-coppock-dotlacil-roelofsen-2022] find the ignorance
contrast graded and dependent on the question under discussion, and [enguehard-2018] derives
the inferences of comparative numerals from granularity. -/
inductive ModifierClass where
  | classA
  | classB
  deriving Repr, DecidableEq

/-- The kinds of numeral modifier in [nouwen-2010]'s survey, by the construction the modifier is
built on. -/
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
  deriving Repr, DecidableEq

/-- The class of each kind. The comparatives are [nouwen-2010]'s model of Class A and the
superlatives and the adverbs of Class B, and the prepositional modifiers follow their spatial
use, a locative preposition giving a Class A modifier and a directional one a Class B
modifier. -/
def ModifierKind.modifierClass : ModifierKind → ModifierClass
  | .comparative | .locative => .classA
  | .superlative | .directional | .adverbial => .classB

/-- A numeral modifier, an expression that combines with a numeral to bound, fix or approximate
the amount it names. -/
structure NumeralModifier where
  /-- The surface form. -/
  form : String
  /-- The construction the modifier is built on, `none` for the exactifiers and approximators,
  which [nouwen-2010]'s survey does not cover. -/
  kind : Option ModifierKind
  /-- The readings the literature makes available, each a modifier of sets of amounts that sends
  the bare numeral's two-sided meaning `{n}` to the amounts verifying the modified numeral. -/
  readings : Set (Modifier (Set ℕ))

namespace NumeralModifier

/-- A numeral modifier denotes its readings. -/
instance : Semantics.Denotes NumeralModifier (Set (Modifier (Set ℕ))) := ⟨readings⟩

open Semantics in
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

/-! ### Exhaustification

On the account of [chierchia-fox-spector-2012] that [spector-2013] discusses, the bare numeral
has the lower-bounded meaning and its two-sided reading comes from a covert exhaustivity
operator, which asserts *at least `m`* and denies *at least `m + 1`*. [kennedy-2015] runs the
derivation the other way, lowering the two-sided meaning to the lower-bounded one. -/

variable {m n : ℕ}

/-- The lower-bounded meaning of `m` exhaustified against the next numeral. -/
def exhNumeral (m : ℕ) : Set ℕ := Comparison.ge.interval m \ Comparison.ge.interval (m + 1)

/-- The exhaustified lower-bounded meaning is the two-sided meaning. -/
theorem exhNumeral_eq (m : ℕ) : exhNumeral m = Comparison.eq.interval m := by
  ext n
  simp only [exhNumeral, Comparison.interval_ge, Comparison.interval_eq, Set.mem_sdiff,
    Set.mem_Ici, Set.mem_singleton_iff]
  omega

instance : DecidablePred (· ∈ exhNumeral m) := fun n ↦
  decidable_of_iff (n = m) (by rw [exhNumeral_eq]; rfl)

/-- Exhaustifying against the next numeral is exhaustifying against the whole scale of higher
numerals, which is an entailment chain (`Exhaustification.exhAgainst_lt_iff_succ`). -/
theorem mem_exhNumeral_iff_exhAgainst :
    n ∈ exhNumeral m ↔
      Exhaustification.exhAgainst (· < ·) (fun k ↦ n ∈ Comparison.ge.interval (m + k)) 0 := by
  rw [Exhaustification.exhAgainst_lt_iff_succ (A := fun k ↦ n ∈ Comparison.ge.interval (m + k))
    (fun j k hjk (h : m + k ≤ n) ↦ show m + j ≤ n by omega) Nat.zero_lt_one fun _ h ↦ h]
  rfl

end Numerals
