module

public import Linglib.Semantics.Degree.Gradability
public import Linglib.Semantics.EvaluativeValence
public import Linglib.Morphology.Morph

/-!
# Adjectives

An adjective lexeme has a surface form, the scalar dimension it measures with the pole it
lexicalizes, any lexically fixed standard, a comparison paradigm and a lexical antonym. Gradability
is not a split of the type: a gradable adjective is one with a dimension, and *wooden* or *former*
is the same type without one, so that its [degree semantics](##Adjective.gradability?), scale and
positive standard are optional, as a verb's are. An `AntonymPair` is the positive and the negative
adjective of one scale, stored once. It is contradictory when [its poles take complementary
standards](##AntonymPair.ComplementaryStandards), the minimum and the maximum of one scale, as
Kennedy and McNally explain for *open* and *closed*; an extreme pair such as *pristine* and *filthy*
leaves a gap even on a closed scale, as Alexandropoulou and Gotzner observe. Without lexical
standards the poles are complementary [exactly on a half-closed
scale](##AntonymPair.complementaryStandards_iff_of_lexicalStandard_none).

## References

* [bobaljik-2012]
* [kennedy-2007]
* [kennedy-mcnally-2005]
* [alexandropoulou-gotzner-2024a]
* [morzycki-2012]
* [beltrama-2025]
* [nouwen-2024]
-/

@[expose] public section

open Morphology

/-! ### Comparison morphology -/

/-- The comparison paradigm of an adjective records its comparative and its superlative, each as
the morphs of the form and empty where the entry gives none. A grade formed with a degree word is a
form of two words, and a suppletive grade is one word on another root, as *better* is. Which roots
of the grades are one root is a source's judgment, recorded with the source in
`Data/Wordlist/`. -/
structure Adjective.Comparison where
  /-- The comparative. -/
  comparative : List Morph := []
  /-- The superlative. -/
  superlative : List Morph := []
  deriving DecidableEq, Repr, BEq

/-! ### The adjective object -/

/-- An adjective lexeme records the syntactic core every adjective shares, its surface form, its
    scalar dimension and pole, its comparison morphology and its lexical antonym. It carries no
    denotation of its own; its degree semantics is `Adjective.gradability?`. Gradability is the
    derived predicate `IsGradable`, and a non-gradable adjective has no dimension. -/
structure Adjective where
  /-- Surface form (citation/positive-grade). -/
  form : String
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- The scalar dimension measured, as a `ScalarDimension` key.
      `none` for classifying/relational adjectives (*wooden*, *former*, *medical*)
      and other non-gradables. -/
  dimension : Option ScalarDimension := none
  /-- The direction of the ordering the adjective imposes on its `dimension`. Antonyms share a
      dimension and reverse the ordering (*tall* positive, *short* negative), so the negative
      member measures on the dual scale. -/
  polarity : Polarity := .positive
  /-- The lexically fixed positive standard, for a partial adjective on a closed scale or for an
      adjective on an open scale whose standard its lexicon fixes, such as the necessity standard
      of *decent* ([beltrama-2025]); `none` takes the scale's default. -/
  lexicalStandard : Option PositiveStandard := none
  /-- The evaluative valence, which determines the degree of an intensifier formed on the
      adjective ([nouwen-2024]). -/
  evaluativeValence : Option EvaluativeValence := none
  /-- Comparative/superlative morphology. -/
  comparison : Adjective.Comparison := {}
  /-- Lexical antonym's surface form, when it has a stable one. -/
  antonymForm : Option String := none
  deriving Repr, DecidableEq, BEq

namespace Adjective

/-- An adjective is gradable when it has a scalar dimension. -/
def IsGradable (a : Adjective) : Prop := a.dimension.isSome = true

instance (a : Adjective) : Decidable a.IsGradable := by unfold IsGradable; infer_instance

/-- The degree semantics of an adjective, `none` for a non-gradable one. -/
def gradability? (a : Adjective) : Option Gradability :=
  a.dimension.map fun d ↦ ⟨d, a.polarity, a.lexicalStandard⟩

/-- The scale of a gradable adjective. -/
def boundedness (a : Adjective) : Option Boundedness := a.gradability?.map (·.boundedness)

/-- The positive standard of a gradable adjective. -/
def standard (a : Adjective) : Option PositiveStandard := a.gradability?.map (·.standard)

/-- The directed scale of a gradable adjective. -/
def directedScale? (a : Adjective) : Option DirectedScale :=
  a.gradability?.map (·.directedScale)

end Adjective

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

namespace AntonymPair

/-- `p.pos` is the positive pole of the pair. -/
def pos (p : AntonymPair) : Adjective where
  form := p.posForm
  dimension := some p.dimension
  comparison := p.posComparison
  lexicalStandard := p.posLexicalStandard
  antonymForm := some p.negForm
  evaluativeValence := p.evaluativeValence

/-- `p.neg` is the negative pole of the pair, which measures on the dual scale. -/
def neg (p : AntonymPair) : Adjective where
  form := p.negForm
  polarity := .negative
  dimension := some p.dimension
  comparison := p.negComparison
  lexicalStandard := p.negLexicalStandard
  antonymForm := some p.posForm
  evaluativeValence := p.evaluativeValence.map EvaluativeValence.flip

@[simp] theorem pos_polarity (p : AntonymPair) : p.pos.polarity = .positive := rfl

@[simp] theorem neg_polarity (p : AntonymPair) : p.neg.polarity = .negative := rfl

@[simp] theorem pos_antonymForm (p : AntonymPair) : p.pos.antonymForm = some p.neg.form := rfl

@[simp] theorem neg_antonymForm (p : AntonymPair) : p.neg.antonymForm = some p.pos.form := rfl

/-- The poles take complementary standards, one the minimum and the other the maximum, so that
they are contradictory and denying one asserts the other, as for *wet* and *dry*
([kennedy-2007] (47)). Any other pair leaves a gap, a relative pair (*large*, *small*) by its
contextual standards and an extreme pair (*pristine*, *filthy*) by standards beyond those of the
weak pair ([morzycki-2012]; [alexandropoulou-gotzner-2024a], fn. 11). -/
def ComplementaryStandards (p : AntonymPair) : Prop :=
  (Gradability.standard ⟨p.dimension, .positive, p.posLexicalStandard⟩).Complementary
    (Gradability.standard ⟨p.dimension, .negative, p.negLexicalStandard⟩)

instance (p : AntonymPair) : Decidable p.ComplementaryStandards :=
  inferInstanceAs (Decidable (PositiveStandard.Complementary _ _))

/-- Without lexically fixed standards, the poles take complementary standards exactly when the
scale has one endpoint. An open scale gives both a contextual standard, which leaves a gap, and a
totally closed one gives both the maximum, as for *full* and *empty*. -/
theorem complementaryStandards_iff_of_lexicalStandard_none (p : AntonymPair)
    (hp : p.posLexicalStandard = none) (hn : p.negLexicalStandard = none) :
    p.ComplementaryStandards ↔
      p.dimension.boundedness = .lowerClosed ∨ p.dimension.boundedness = .upperClosed :=
  Gradability.complementary_standard_iff (g := ⟨p.dimension, .positive, p.posLexicalStandard⟩)
    (h := ⟨p.dimension, .negative, p.negLexicalStandard⟩) rfl rfl rfl hp hn

end AntonymPair
