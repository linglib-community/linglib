module

public import Linglib.Semantics.Degree.Antonymy
public import Linglib.Semantics.Degree.Scale
public import Linglib.Morphology.Morph

/-!
# Adjectives

An adjective lexeme has a surface form, the scalar dimension it measures with the pole it
lexicalizes, a comparison paradigm and a lexical antonym. Gradability is not a split of the
type: a gradable adjective is one with a dimension, and *wooden* or *former* is the same type
without one. The degree semantics, with the positive standard and the Kennedy class, is
`GradableAdjective` in `Semantics/Degree/Adjective.lean`.

## Main definitions

* `Adjective.Comparison`: the comparative and the superlative of an adjective as morphs.
* `Adjective`: the lexeme, with `Adjective.IsGradable`.

## References

* [bobaljik-2012]
-/

@[expose] public section

open Degree Morphology

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
    denotation of its own; the degree semantics is `GradableAdjective` in
    `Semantics/Degree/Adjective.lean`. Gradability is the derived predicate `IsGradable`, and a
    non-gradable adjective has no dimension. -/
structure Adjective where
  /-- Surface form (citation/positive-grade). -/
  form : String
  /-- Native script form, when distinct. -/
  script : Option String := none
  /-- The scalar dimension measured, as a `Degree.ScalarDimension` key.
      `none` for classifying/relational adjectives (*wooden*, *former*, *medical*)
      and other non-gradables. -/
  dimension : Option ScalarDimension := none
  /-- The direction of the ordering the adjective imposes on its `dimension`. Antonyms share a
      dimension and reverse the ordering (*tall* positive, *short* negative), so the negative
      member measures on the dual scale. -/
  polarity : Polarity := .positive
  /-- Comparative/superlative morphology. -/
  comparison : Adjective.Comparison := {}
  /-- Lexical antonym's surface form, when it has a stable one. -/
  antonymForm : Option String := none
  deriving Repr, DecidableEq, BEq

namespace Adjective

/-- An adjective is gradable when it has a scalar dimension. -/
def IsGradable (a : Adjective) : Prop := a.dimension.isSome = true

instance (a : Adjective) : Decidable a.IsGradable := by unfold IsGradable; infer_instance

end Adjective
