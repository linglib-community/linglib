/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Exhaustification.Pointwise
public import Linglib.Semantics.Quantification.Individual

/-!
# Numeral meanings

A bare numeral and its modifications *more than*, *fewer than*, *at least* and *at most* are the
five comparisons of `Degree.Comparison`. On Kennedy's de-Fregean semantics the form with comparison
`c` and number `m` is the degree quantifier `Degree.MaxIn (c.interval m)`, so the bare numeral
`MaxIn {m}` is two-sided; in the tradition of Horn it is the lower-bounded `NP.individual m`. Each
reading derives the other: [Partee's `BE` lowers a de-Fregean form to its interval](##BE_maxIn) and
[existential closure then gives the lower-bounded numeral](##some_BE_maxIn_singleton), which the
two-sided one [asymmetrically entails](##maxIn_singleton_lt_individual), while [exhaustifying the
lower-bounded numeral against the higher ones restores the de-Fregean
one](##maxIn_singleton_iff_exhAgainst), on counts [the exact reading](##exhAgainst_ge_iff). A
numeral modifier is a lexical item whose readings are modifiers of sets of amounts, and Nouwen's
two classes of modifier are read off the construction it is built on.

## References

* [kennedy-2015]
* [horn-1972]
* [partee-1987]
* [spector-2013]
* [chierchia-fox-spector-2012]
* [nouwen-2010]
* [schwarz-buccola-hamilton-2012]
* [cremers-coppock-dotlacil-roelofsen-2022]
* [enguehard-2018]
-/

@[expose] public section

namespace Numerals

open Degree Exhaustification Quantifier

/-! ### The two readings of a bare numeral -/

section Readings

variable {D : Type*}

/-- Partee's `BE` lowers the de-Fregean form with interval `U` to the property of lying in `U`, as
`BE(three)` is the property of being three ([kennedy-2015], (39)). -/
theorem BE_maxIn [Preorder D] (U : Set D) : NP.BE (MaxIn U) = (· ∈ U) :=
  funext fun x ↦ propext
    ⟨fun ⟨_, hm, h⟩ ↦ (h.1 : _ = x) ▸ hm, fun hx ↦ ⟨x, hx, isGreatest_singleton⟩⟩

/-- Existential closure over the lowered bare numeral is the individual of the number, the
lower-bounded reading ([kennedy-2015], (40b) and fn. 3). -/
theorem some_BE_maxIn_singleton [Preorder D] (m : D) :
    GQ.some (NP.BE (MaxIn {m})) = NP.individual m := by
  rw [BE_maxIn]
  exact NP.some_ident m

/-- On a scale without a top degree the two-sided bare numeral asymmetrically entails the
lower-bounded one. -/
theorem maxIn_singleton_lt_individual [Preorder D] [NoMaxOrder D] (m : D) :
    MaxIn {m} < (NP.individual m : Set D → Prop) :=
  lt_of_le_not_ge (fun _ h ↦ (maxIn_singleton.1 h).1) fun h ↦
    let ⟨a, ha⟩ := exists_gt m
    ha.not_ge ((maxIn_singleton.1 (h (Set.Iic a) ha.le)).2 le_rfl)

/-- Exhaustified against the higher numerals, the lower-bounded bare numeral is the de-Fregean
one, on any degree property: exhaustification is the meaning-changing operation that
[kennedy-2015] (p. 10:20) says the two-sided reading needs if the singular term is basic. -/
theorem maxIn_singleton_iff_exhAgainst [LinearOrder D] {X : Set D} {m : D} :
    MaxIn {m} X ↔ exhAgainst (· < ·) (· ∈ X) m :=
  maxIn_singleton.trans <| and_congr_right' ⟨fun h _ hm hmX ↦ (h hmX).not_gt hm,
    fun h n hnX ↦ not_lt.1 fun hn ↦ h n hn hnX⟩

/-- Exhaustified against the higher numerals, *at least `m`* is true of `a` exactly when `a` is
`m`, the two-sided reading of the bare numeral, on any partially ordered scale. -/
theorem exhAgainst_ge_iff [PartialOrder D] {a m : D} :
    exhAgainst (· < ·) (fun j ↦ a ∈ Comparison.ge.interval j) m ↔
      a ∈ Comparison.eq.interval m :=
  exhAgainst_lt_iff_maximal.trans <| by simp [eq_comm]

end Readings

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
  deriving Repr, DecidableEq

/-- The class of each kind, after [nouwen-2010]'s tentative classification of the English
modifiers. The comparatives are his model of Class A and the superlatives and the adverbs of
Class B, and the prepositional modifiers follow their spatial use, a locative preposition giving a
Class A modifier and a directional one a Class B modifier. *Over* is Class A although its usual
spatial sense is directional, which Nouwen puts down to numeral modifiers using only vertical
senses. -/
def ModifierKind.modifierClass : ModifierKind → ModifierClass
  | .comparative | .locative => .classA
  | .superlative | .directional | .adverbial => .classB

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
