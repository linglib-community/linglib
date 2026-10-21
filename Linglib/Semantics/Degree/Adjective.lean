module

public import Linglib.Semantics.Degree.Boundedness
public import Linglib.Semantics.Degree.Scale
public import Linglib.Semantics.Degree.Antonymy
public import Linglib.Syntax.Category.Adjective.Basic

/-!
# Gradable adjectives

This file defines `Degree.GradableAdjective`, a syntactic adjective together with its degree
semantics. The scale an adjective measures on, its positive standard and its Kennedy class are
derived from its dimension, its polarity and any lexically fixed standard, so that *wet* and *dry*
share one scale and differ only in pole. The file also defines antonym pairs and the ways a
multidimensional adjective binds its dimensions.

An antonym pair is contradictory when its poles take complementary standards, the minimum and the
maximum of one scale, as Kennedy and McNally explain for *open* and *closed*. A pair of extreme
adjectives such as *pristine* and *filthy* leaves a gap even on a closed scale, as Alexandropoulou
and Gotzner observe, since its standards lie beyond those of the weak pair; the relation is read
off the standards rather than stored. How a standard is interpreted, as a literal endpoint or
relative to a contextual range, is left to the studies.

## Main definitions

* `AdjectiveClass`: Kennedy's classes of gradable adjectives.
* `GradableAdjective`: a syntactic adjective with its degree semantics.
* `GradableAdjective.boundedness`: the scale an adjective measures on.
* `GradableAdjective.standard`: the positive standard of an adjective.
* `AntonymPair`: the two polar adjectives of one scale.
* `AntonymPair.ComplementaryStandards`: the poles take the minimum and the maximum, and so are
  contradictory, where any other pair leaves a gap and is contrary; without lexical standards
  this holds exactly on a half-closed scale
  (`AntonymPair.complementaryStandards_iff_of_lexicalStandard_none`).
* `DimensionBindingType`: how a multidimensional adjective binds its dimensions.

## References

* [C. Kennedy, *Vagueness and Grammar: The Semantics of Relative and Absolute Gradable Adjectives*
  (2007)][kennedy-2007]
* [C. Kennedy and L. McNally, *Scale Structure, Degree Modification, and the Semantics of Gradable
  Predicates* (2005)][kennedy-mcnally-2005]
* [S. Alexandropoulou and N. Gotzner, *The Interpretation of Relative and Absolute Adjectives Under
  Negation* (2024)][alexandropoulou-gotzner-2024a]
* [M. Morzycki, *Adjectival Extremeness: Degree Modification and Contextually Restricted Scales*
  (2012)][morzycki-2012]
* [G. W. Sassoon, *A Typology of Multidimensional Adjectives* (2013)][sassoon-2013]
* [A. Beltrama, *Evaluation, Thresholds, and Practical Commitments: The Grammar of Adjectival
  Mildness* (2025)][beltrama-2025]
* [R. Nouwen, *The Semantics and Probabilistic Pragmatics of Deadjectival Intensifiers*
  (2024)][nouwen-2024]
* [B. Levin, *The door pushed open: an English intransitive resultative construction with
  transitive-only verbs* (2026)][levin-2026]
-/

@[expose] public section

namespace Degree

/-! ### Kennedy's adjective classes -/

/-- An adjective class is Kennedy's classification of an adjective by its scale structure and
standard ([kennedy-2007], [kennedy-mcnally-2005]), with further classes for the lexical necessity
and extreme standards and for non-gradable adjectives. -/
inductive AdjectiveClass where
  /-- The standard varies with a comparison class, as for *tall*, *expensive* and *big*. -/
  | relative
  /-- The standard is the maximum of the scale, as for *full*, *straight*, *closed* and *dry*. -/
  | absoluteMaximum
  /-- The standard is the minimum of the scale, as for *wet*, *bent*, *open* and *dirty*. -/
  | absoluteMinimum
  /-- The standard is a necessity threshold, as for *decent* and *acceptable* ([beltrama-2025]). -/
  | mildlyPositive
  /-- The standard lies beyond that of the weak adjective on the same pole, as for *gigantic* and
  *pristine* ([morzycki-2012]). -/
  | extreme
  /-- The adjective has no degree argument and no scale, as for *atomic*, *prime*, *deceased* and
  *pregnant*; an adjective that is not gradable belongs here rather than in a gradable class. -/
  | nonGradable
  deriving Repr, DecidableEq

/-! ### The gradable adjective -/

/-- A spatial configuration type classifies the spatial state an adjective describes in a
    resultative construction ([levin-2026]). Only adjectives describing spatially instantiated
    states license intransitive *push open* resultatives. -/
inductive SpatialConfigType where
  | barrierConfig   -- open, closed, shut: config relative to frame
  | unattachment    -- free, loose: freedom from spatial contiguity
  | surfaceOrient   -- flat: orientation relative to reference surface
  deriving DecidableEq, Repr

/-- A **gradable adjective** is a syntactic adjective together with its degree semantics,
    namely any lexically fixed standard, its resultative spatial configuration ([levin-2026]) and
    its evaluative valence ([nouwen-2024]). Its scale, positive standard and adjective class are
    derived from its dimension and polarity. -/
structure GradableAdjective extends Adjective where
  /-- The lexically fixed positive standard, for a partial adjective on a closed scale or for an
      adjective on an open scale whose standard its lexicon fixes, such as the necessity standard
      of *decent* ([beltrama-2025]); `none` takes the scale's default. -/
  lexicalStandard : Option PositiveStandard := none
  /-- Resultative spatial-configuration class ([levin-2026]). -/
  spatialConfigType : Option SpatialConfigType := none
  /-- The evaluative valence, which determines the degree of an intensifier formed on the
      adjective ([nouwen-2024]). -/
  evaluativeValence : Option EvaluativeValence := none
  deriving Repr

namespace GradableAdjective

/-- The scale an adjective measures on is its dimension's, dualized for the negative member of
an antonym pair, and open for a non-gradable adjective, which has none. -/
def boundedness (g : GradableAdjective) : Boundedness :=
  (g.dimension.map fun d ↦ g.polarity • d.boundedness).getD .open_

/-- The positive standard of an adjective is its lexically fixed one if any, and otherwise its
scale's default. -/
def standard (g : GradableAdjective) : PositiveStandard :=
  g.lexicalStandard.getD g.boundedness.defaultStandard

/-- Without a lexically fixed standard, the standard is one the scale admits. -/
theorem admits_standard (g : GradableAdjective) (h : g.lexicalStandard = none) :
    g.boundedness.Admits g.standard := by
  simp [standard, h, Boundedness.admits_defaultStandard]

/-- Kennedy's class of an adjective is read off its standard, and is non-gradable exactly when
    the adjective has no dimension ([kennedy-2007], [kennedy-mcnally-2005]). -/
def adjectiveClass (g : GradableAdjective) : AdjectiveClass :=
  match g.dimension with
  | none => .nonGradable
  | some _ =>
    match g.standard with
    | .contextual  => .relative
    | .minEndpoint => .absoluteMinimum
    | .maxEndpoint => .absoluteMaximum
    | .necessity   => .mildlyPositive
    | .extreme     => .extreme

/-- An adjective is relative when its class is the relative one. -/
def IsRelative (g : GradableAdjective) : Prop := g.adjectiveClass = .relative

instance (g : GradableAdjective) : Decidable g.IsRelative := by
  unfold IsRelative; infer_instance

end GradableAdjective

/-! ### Antonym pairs -/

/-- An **antonym pair** is the positive and the negative polar adjective of one scale, each the
other's lexical antonym. The shared data is stored once, and the two adjectives are
`AntonymPair.pos` and `AntonymPair.neg`. -/
structure AntonymPair where
  /-- The scale both poles measure on. -/
  dimension : ScalarDimension
  /-- The positive pole's surface form. -/
  posForm : String
  /-- The negative pole's surface form. -/
  negForm : String
  /-- The positive pole's comparison paradigm. -/
  posComparison : Adjective.Comparison := {}
  /-- The negative pole's comparison paradigm. -/
  negComparison : Adjective.Comparison := {}
  /-- The positive pole's lexically fixed standard, when it departs from the scale's default, is
      for instance the minimum for a partial adjective like *open* on a closed scale, or the
      extreme standard of *gigantic*. -/
  posLexicalStandard : Option PositiveStandard := none
  /-- The negative pole's lexically fixed standard, when it departs from the dual's default. -/
  negLexicalStandard : Option PositiveStandard := none
  /-- The positive pole's evaluative valence; the negative pole's is its `flip`. -/
  evaluativeValence : Option EvaluativeValence := none
  /-- The resultative spatial-configuration class the poles share. -/
  spatialConfigType : Option SpatialConfigType := none

namespace AntonymPair

/-- `p.pos` is the positive pole of the pair. -/
def pos (p : AntonymPair) : GradableAdjective where
  form := p.posForm
  dimension := some p.dimension
  comparison := p.posComparison
  lexicalStandard := p.posLexicalStandard
  antonymForm := some p.negForm
  evaluativeValence := p.evaluativeValence
  spatialConfigType := p.spatialConfigType

/-- `p.neg` is the negative pole of the pair, which measures on the dual scale. -/
def neg (p : AntonymPair) : GradableAdjective where
  form := p.negForm
  polarity := .negative
  dimension := some p.dimension
  comparison := p.negComparison
  lexicalStandard := p.negLexicalStandard
  antonymForm := some p.posForm
  evaluativeValence := p.evaluativeValence.map EvaluativeValence.flip
  spatialConfigType := p.spatialConfigType

@[simp] theorem pos_polarity (p : AntonymPair) : p.pos.polarity = .positive := rfl

@[simp] theorem neg_polarity (p : AntonymPair) : p.neg.polarity = .negative := rfl

/-- The poles name each other as antonyms. -/
@[simp] theorem pos_antonymForm (p : AntonymPair) : p.pos.antonymForm = some p.neg.form := rfl

@[simp] theorem neg_antonymForm (p : AntonymPair) : p.neg.antonymForm = some p.pos.form := rfl

/-- The poles take complementary standards, one the minimum and the other the maximum, so that
they are contradictory and denying one asserts the other, as for *wet* and *dry*
([kennedy-2007] (47)). Any other pair leaves a gap, a relative pair (*large*, *small*) by its
contextual standards and an extreme pair (*pristine*, *filthy*) by standards beyond those of the
weak pair ([morzycki-2012]; [alexandropoulou-gotzner-2024a], fn. 11). -/
def ComplementaryStandards (p : AntonymPair) : Prop :=
  p.pos.standard.Complementary p.neg.standard

instance (p : AntonymPair) : Decidable p.ComplementaryStandards := by
  unfold ComplementaryStandards; infer_instance

/-- Without lexically fixed standards, the poles take complementary standards exactly when the
scale has one endpoint. An open scale gives both a contextual standard, which leaves a gap, and a
totally closed one gives both the maximum, as for *full* and *empty*. -/
theorem complementaryStandards_iff_of_lexicalStandard_none (p : AntonymPair)
    (hp : p.posLexicalStandard = none) (hn : p.negLexicalStandard = none) :
    p.ComplementaryStandards ↔
      p.dimension.boundedness = .lowerClosed ∨ p.dimension.boundedness = .upperClosed := by
  simpa [ComplementaryStandards, GradableAdjective.standard, GradableAdjective.boundedness, pos,
    neg, hp, hn] using Boundedness.complementary_defaultStandard_dual_iff

end AntonymPair

/-! ### Multidimensional adjectives ([sassoon-2013]) -/

/-- A multidimensional adjective binds its dimensions conjunctively, disjunctively, or either way
depending on context ([sassoon-2013]). -/
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
  | .mixed       => .mixed

theorem negate_involutive (b : DimensionBindingType) :
    b.negate.negate = b := by cases b <;> rfl

/-- The binding type a standard predicts is conjunctive for the maximum standard of a total
    adjective, disjunctive for the minimum standard of a partial one, and mixed for a contextual
    standard ([sassoon-2013], Hypothesis set 3, (23)). -/
def predictedBinding : Degree.PositiveStandard → DimensionBindingType
  | .maxEndpoint => .conjunctive
  | .minEndpoint => .disjunctive
  | .contextual  => .mixed
  | .necessity   => .mixed   -- evaluative; context-dependent like contextual
  | .extreme     => .mixed   -- context-dependent like contextual

end Degree
