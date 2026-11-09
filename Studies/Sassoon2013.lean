module

public import Linglib.Semantics.Aggregation.Rules
public import Linglib.Semantics.Quantification.Basic
public import Linglib.Syntax.Category.Adjective.Basic
public import Linglib.Data.Examples.Sassoon2013
public import Linglib.Data.Examples.Readers

/-!
# Sassoon (2013): A Typology of Multidimensional Adjectives

This file formalizes the paper's corpus typology of multidimensional adjectives. A multidimensional
adjective binds its dimensions with an implicit quantifier, and exception phrases reveal its force:
*healthy except for high blood pressure* operates on a universal over dimensions, so an adjective is
conjunctive when dimensional exception phrases occur with it in positive contexts, disjunctive when
they occur under negation, and mixed when both occur alike; a type denotes the determiners it may
bind by (`DimensionBindingType.dets`), *every*, *some*, or either as context decides. The paper's
criterion classifies an adjective from the frequencies of dimensional uses in the two contexts,
conjunctive or disjunctive when one is at least three times the other (`classify`), and applied to
its sample it yields the paper's three lists (`typology`). Two predictors are tested. Antonym
polarity: under a negation theory of antonymy the negative member of a pair is the negation of the
positive one, so De Morgan turns a universal over dimensions into an existential, so that the
negative antonym binds by the duals of the positive one's determiners
(`DimensionBindingType.dets_negate`); the clearly conjunctive adjectives are all judged positive and
the clearly disjunctive ones negative (`polarity_predicts_binding`), and within an antonym pair the
two are never both clearly bound the same way (`antonyms_negate`). Standard type: total adjectives
should be conjunctive and partial ones disjunctive, the mechanism being `predictedBinding`; by the
inference tests no total adjective is disjunctive, but partial adjectives include conjunctive ones,
so the biconditional fails and the paper reports only a correlation with modifier-based totality
(`total_not_disjunctive`, `partial_conjunctive_exists`). Comparatives inherit the binding of their
base except that *worse* is milder than *bad* (`comparatives_inherit`); the readings *in more
respects* and *on average* lie between the universal and the existential comparative
(`comparative_every_le_majority`, `majority_le_comparative_some`).

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

/-- A multidimensional adjective binds its dimensions conjunctively, disjunctively, or either way
depending on context. -/
inductive DimensionBindingType where
  /-- The entity meets the standard in every dimension, as for *healthy*. -/
  | conjunctive
  /-- The entity meets the standard in some dimension, as for *sick*. -/
  | disjunctive
  /-- Context decides between the two, as for *intelligent*. -/
  | mixed
  deriving Repr, DecidableEq

/-- `b.negate` is the binding type predicted for a negative antonym whose positive counterpart
binds by `b`, by De Morgan's laws under the negation theory of antonymy. -/
def DimensionBindingType.negate : DimensionBindingType → DimensionBindingType
  | .conjunctive => .disjunctive
  | .disjunctive => .conjunctive
  | .mixed => .mixed

open Quantifier

/-- The determiners by which an adjective of a binding type may bind its dimensions, by
Hypothesis set 1 ((4)): *every* for a conjunctive adjective, *some* for a disjunctive one, and
either, as pragmatics decides, for a mixed one. An entity is A when such a determiner, restricted
to the adjective's dimensions, holds of those on which the entity reaches the standard. -/
def DimensionBindingType.dets {ι : Type*} : DimensionBindingType → Set (Det ι)
  | .conjunctive => {Det.every}
  | .disjunctive => {Det.some}
  | .mixed => {Det.every, Det.some}

-- De Morgan: the negative antonym binds by the duals of its positive counterpart's determiners
theorem DimensionBindingType.dets_negate {ι : Type*} (b : DimensionBindingType) :
    (b.negate.dets : Set (Det ι)) = Det.dual '' b.dets := by
  cases b <;> simp [negate, dets, Det.dual_every, Det.dual_some, Set.pair_comm]

/-- The binding type a standard predicts is conjunctive for the maximum standard of a total
adjective, disjunctive for the minimum standard of a partial one, and mixed for a contextual
standard (Hypothesis set 3, (23)). Necessity and extreme standards, which the paper does not treat,
are context-dependent like contextual ones. -/
def predictedBinding : PositiveStandard → DimensionBindingType
  | .maxEndpoint => .conjunctive
  | .minEndpoint => .disjunctive
  | .contextual | .necessity | .extreme => .mixed


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

section Comparative

open Aggregation

variable {ι O K : Type*}

/-- Sassoon's comparative of an adjective that binds its dimensions `D` by the determiner `d`:
`x` is F-er than `y` when `d` holds, among the dimensions in `D`, of those on which `x` is F-er
(p. 368). -/
def comparative [LT K] (d : Det ι) (D : Set ι) : Rule ι O K := ofRel fun p q ↦ d D {i | q i < p i}

variable [Fintype ι] [LinearOrder K]

-- p. 369: *healthier in more respects* is weaker than *healthier in every respect*
theorem comparative_every_le_majority [Nonempty ι] :
    (comparative Det.every .univ : Rule ι O K) ≤ fun v ↦ AsymmRel (majority v) :=
  fun v x y h ↦ majority_weakPareto v x y fun i ↦ h (Set.mem_univ i)

-- p. 369: *worse in more respects* is stronger than *worse in some respect*
theorem majority_le_comparative_some :
    (fun v ↦ AsymmRel (majority v)) ≤ (comparative Det.some .univ : Rule ι O K) := by
  intro v x y h
  by_contra hne
  have hall (i : ι) : v x i ≤ v y i := not_lt.1 fun hi ↦ hne ⟨i, Set.mem_univ i, hi⟩
  refine h.2 ?_
  rw [majority_apply, Finset.filter_true_of_mem fun i _ ↦ hall i]
  exact Finset.card_le_univ _

variable [Field K] [IsStrictOrderedRing K]

-- p. 369: *healthier on average* is weaker than *healthier in every respect*
theorem comparative_every_le_utilitarian [Nonempty ι] :
    (comparative Det.every .univ : Rule ι O K) ≤ fun v ↦ AsymmRel (utilitarian 1 v) :=
  fun v x y h ↦ utilitarian_weakPareto 1 (fun _ ↦ zero_le_one) ⟨Classical.arbitrary ι, one_pos⟩
    v x y fun i ↦ h (Set.mem_univ i)

-- p. 369: *worse on average* is stronger than *worse in some respect*
theorem utilitarian_le_comparative_some :
    (fun v ↦ AsymmRel (utilitarian 1 v)) ≤ (comparative Det.some .univ : Rule ι O K) := by
  intro v x y h
  by_contra hne
  exact h.2 (dotProduct_le_dotProduct_of_nonneg_left
    (fun i ↦ not_lt.1 fun hi ↦ hne ⟨i, Set.mem_univ i, hi⟩) fun _ ↦ zero_le_one)

end Comparative

theorem comparatives_inherit :
    ∀ x ∈ Examples.all, ∀ f ∈ x.feature? "base", ∀ y ∈ rowOf f,
      (binding? y ≠ some .disjunctive → binding? x = binding? y) ∧
        (binding? y = some .disjunctive → binding? x = some .mixed) := by
  decide +kernel

end Sassoon2013
