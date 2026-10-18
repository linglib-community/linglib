/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Core.Order.Flat
public import Linglib.Core.Order.PartialUnify
public import Linglib.Data.UD.Features
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Number.Basic
public import Linglib.Syntax.Person.Basic

/-!
# Token features

The morphosyntactic features a word token carries: the agreement dimensions, valued in the
analytical inventories `Person`, `Number`, `Gender` and `Case`, and the nominal and verbal
features of the Universal Dependencies annotation, definiteness, degree, pronoun type,
reflexivity, verb form, tense, aspect, mood, voice and polarity, valued in the tag inventories
until an analytical one exists. A token's features give each feature a value or `⊥`, a slot of
the flat order, so subsumption, unification and generalization are the pointwise order, partial
join and meet; the Universal Dependencies annotation of a token is the matter of
`Morphology/Word/UD.lean`.

## Main declarations

* `Morphology.Feature`, `Morphology.Feature.Value`: the features and their value types.
* `Morphology.Features`: the bundle, with the constructor `Features.of` naming the values it
  specifies.
* `Morphology.Features.IsWh`: an interrogative or relative pro-form.

## References

* [de-marneffe-zeman-2021]
* [shieber-1986]
-/

@[expose] public section

namespace Morphology

/-- The morphosyntactic features of a token. -/
inductive Feature where
  | person | number | gender | case | definiteness | degree | pronType | reflex
  | verbForm | tense | aspect | mood | voice | polarity
  deriving DecidableEq, Repr, Fintype

/-- A feature takes its values in the analytical inventory for an agreement dimension and in the
Universal Dependencies tags otherwise, reflexivity being privative. -/
abbrev Feature.Value : Feature → Type
  | .person => Person
  | .number => Number
  | .gender => Gender
  | .case => Case
  | .definiteness => UD.Definite
  | .degree => UD.Degree
  | .pronType => UD.PronType
  | .reflex => Unit
  | .verbForm => UD.VerbForm
  | .tense => UD.Tense
  | .aspect => UD.Aspect
  | .mood => UD.Mood
  | .voice => UD.Voice
  | .polarity => UD.Polarity

instance (t : Feature) : DecidableEq t.Value := by cases t <;> exact inferInstance

instance (t : Feature) : Repr t.Value := by cases t <;> exact inferInstance

/-- A token's features give each feature a value or `⊥`. -/
abbrev Features := (f : Feature) → Flat f.Value

namespace Features

/-- The bundle specifying the named values and nothing else. -/
def of (person : Option Person := none) (number : Option Number := none)
    (gender : Option Gender := none) (case_ : Option Case := none)
    (definiteness : Option UD.Definite := none) (degree : Option UD.Degree := none)
    (pronType : Option UD.PronType := none) (reflex : Option Unit := none)
    (verbForm : Option UD.VerbForm := none) (tense : Option UD.Tense := none)
    (aspect : Option UD.Aspect := none) (mood : Option UD.Mood := none)
    (voice : Option UD.Voice := none) (polarity : Option UD.Polarity := none) : Features
  | .person => person
  | .number => number
  | .gender => gender
  | .case => case_
  | .definiteness => definiteness
  | .degree => degree
  | .pronType => pronType
  | .reflex => reflex
  | .verbForm => verbForm
  | .tense => tense
  | .aspect => aspect
  | .mood => mood
  | .voice => voice
  | .polarity => polarity

instance : Repr Features where
  reprPrec f _ :=
    repr (f .person, f .number, f .gender, f .case, f .definiteness, f .degree, f .pronType,
      f .reflex, f .verbForm, f .tense, f .aspect, f .mood, f .voice, f .polarity)

/-- The token is an interrogative or relative pro-form. -/
def IsWh (f : Features) : Prop := f .pronType = some .Int ∨ f .pronType = some .Rel

instance (f : Features) : Decidable f.IsWh := inferInstanceAs (Decidable (_ ∨ _))

end Features

end Morphology
