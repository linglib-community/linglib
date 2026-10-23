module

public import Linglib.Semantics.Degree.Adjective
public import Linglib.Data.Examples.Sassoon2013

/-!
# Sassoon (2013): A Typology of Multidimensional Adjectives

This file formalizes the paper's corpus typology of multidimensional adjectives. A
multidimensional adjective binds its dimensions with an implicit quantifier, and exception
phrases reveal its force: *healthy except for high blood pressure* operates on a universal over
dimensions, so an adjective is conjunctive when dimensional exception phrases occur with it in
positive contexts, disjunctive when they occur under negation, and mixed when both occur
alike. The paper's criterion classifies an adjective from the frequencies of dimensional uses
in the two contexts, conjunctive or disjunctive when one is at least three times the other
(`classify`), and applied to its sample it yields the paper's three lists (`typology`). Two
predictors are tested. Antonym polarity: under a negation theory of antonymy the negative
member of a pair is the negation of the positive one, so De Morgan turns a universal over
dimensions into an existential (`DimensionBindingType.negate`); the
clearly conjunctive adjectives are all judged positive and the clearly disjunctive ones
negative (`polarity_predicts_binding`), and within an antonym pair the two are never both
clearly bound the same way (`antonyms_negate`). Standard type: total adjectives should be
conjunctive and partial ones disjunctive, the mechanism being the substrate's
`predictedBinding`; by the inference tests no total adjective is disjunctive, but partial
adjectives include conjunctive ones, so the biconditional fails and the paper reports only a
correlation with modifier-based totality (`total_not_disjunctive`,
`partial_conjunctive_exists`). Comparatives inherit the binding of their base except that
*worse* is milder than *bad* (`comparatives_inherit`).

## Implementation notes

The rows carry the paper's tables: the percentages of dimensional uses in positive and
negated contexts, the polarity means in hundredths, the normalized totality index and the
inference-test standard type. The correlations the paper reports between polarity and
normalized conjunctivity and between totality and conjunctivity are not formalized.

## References

* [sassoon-2013]
* [kennedy-mcnally-2005]
* [heim-2006]
* [buring-2007]
-/

@[expose] public section

namespace Sassoon2013

open Degree

/-- An adjective is conjunctive when its dimensional uses in positive contexts are at least three
times those in negated contexts, disjunctive in the converse case, and mixed otherwise. -/
def classify (conj disj : ℕ) : DimensionBindingType :=
  if 3 * disj ≤ conj then .conjunctive else if 3 * conj ≤ disj then .disjunctive else .mixed

/-- A sampled adjective's binding type from its corpus percentages. -/
def binding? (x : Datum) : Option DimensionBindingType :=
  (x.nat? "conj").bind fun c ↦ (x.nat? "disj").map (classify c)

/-- The row of an adjective. -/
def rowOf (form : String) : Option Datum :=
  Examples.all.find? (·.primaryText == form)

theorem typology :
    ∀ x ∈ Examples.all, ∀ b ∈ binding? x,
      (b = .conjunctive ↔
          x.primaryText ∈ ["normal", "typical", "healthy", "familiar", "healthier"]) ∧
        (b = .disjunctive ↔
          x.primaryText ∈ ["bad", "sick", "atypical", "abnormal", "different"]) := by
  decide +kernel

/-! ### Antonym polarity -/

theorem polarity_judgments :
    ∀ x ∈ Examples.all, ∀ p ∈ x.nat? "polarity",
      (x.feature? "positive" = some "true" ↔ 400 < p) := by
  decide +kernel

theorem polarity_predicts_binding :
    ∀ x ∈ Examples.all, ∀ b ∈ binding? x, ∀ p ∈ x.nat? "polarity",
      (b = .conjunctive → 400 < p) ∧ (b = .disjunctive → p < 400) := by
  decide +kernel

theorem antonyms_negate :
    ∀ x ∈ Examples.all, ∀ a ∈ x.feature? "antonym", ∀ y ∈ rowOf a,
      ∀ b ∈ binding? x, ∀ b' ∈ binding? y, b ≠ .mixed → b' ≠ .mixed → b' = b.negate := by
  decide +kernel

/-! ### Standard type -/

/-- The paper's standard types by the inference tests, as positive standards. -/
def standards : List (String × PositiveStandard) :=
  [("total", .maxEndpoint), ("partial", .minEndpoint), ("relative", .contextual)]

theorem total_not_disjunctive :
    ∀ x ∈ Examples.all, ∀ s ∈ x.parse? "standard" standards, ∀ b ∈ binding? x,
      s = .maxEndpoint → b ≠ .disjunctive := by
  decide +kernel

theorem partial_conjunctive_exists :
    ∃ x ∈ Examples.all, x.parse? "standard" standards = some .minEndpoint ∧
      binding? x = some .conjunctive ∧ predictedBinding .minEndpoint ≠ .conjunctive := by
  decide +kernel

/-! ### Comparatives -/

theorem comparatives_inherit :
    ∀ x ∈ Examples.all, ∀ f ∈ x.feature? "base", ∀ y ∈ rowOf f,
      (binding? y ≠ some .disjunctive → binding? x = binding? y) ∧
        (binding? y = some .disjunctive → binding? x = some .mixed) := by
  decide +kernel

end Sassoon2013
