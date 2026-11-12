/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Powerset
public import Linglib.Syntax.Person.Basic

/-!
# Accessibility marking

This file defines Ariel's Accessibility Marking Scale. An accessibility level is a class of
referring expression, from a modified full name to a zero, and the scale orders the classes by the
accessibility of the referent they code. Three partially overlapping criteria motivate the scale,
and each is read here off the features of a form class and compared rather than counted.

## Main definitions

* `Discourse.AccessibilityLevel`: the scale, as a linear order.
* `AccessibilityLevel.informativity`: the information a form incorporates, ordered by inclusion.
* `AccessibilityLevel.rigidity`: how unequivocally a name picks out its referent.
* `AccessibilityLevel.attenuation`: the phonological size of a form.
* `AccessibilityLevel.criteria`: the three jointly, in the product order.

## Implementation notes

The scale is the ordering of English form classes, taken as data. The criteria are not
individually antitone along it, and which comparisons they predict jointly is the business of
`Studies/Ariel2001.lean`. Ariel says which distinctions each criterion draws, not what its values
are: `Information` and `Attenuation` name just enough values to draw them, and a bare
demonstrative is given the size of a stressed pronoun.

## References

* [ariel-1990]
* [ariel-2001]
-/

@[expose] public section

namespace Discourse

/-- An accessibility level is a class of referring expression on the Accessibility Marking
Scale of [ariel-1990], from the least to the most accessible referent it codes. -/
inductive AccessibilityLevel where
  /-- A modified full name, *the former governor of Alaska, Sarah Palin*. -/
  | fullNameMod
  /-- A full name, *Sarah Palin*. -/
  | fullName
  /-- A long definite description, *the former governor of Alaska*. -/
  | longDefDescription
  /-- A short definite description, *the governor*. -/
  | shortDefDescription
  /-- A last name, *Palin*. -/
  | lastName
  /-- A first name, *Sarah*. -/
  | firstName
  /-- A modified distal demonstrative phrase, *that tall woman over there*. -/
  | distalDemMod
  /-- A modified proximate demonstrative phrase, *this tall woman*. -/
  | proxDemMod
  /-- A distal demonstrative phrase, *that woman*. -/
  | distalDemNP
  /-- A proximate demonstrative phrase, *this woman*. -/
  | proxDemNP
  /-- A distal demonstrative, *that*. -/
  | distalDem
  /-- A proximate demonstrative, *this*. -/
  | proxDem
  /-- A stressed pronoun with a pointing gesture. -/
  | stressedPronGesture
  /-- A stressed pronoun, *SHE*. -/
  | stressedPron
  /-- An unstressed pronoun, *she*. -/
  | unstressedPron
  /-- A cliticized pronoun, *'er*. -/
  | cliticizedPron
  /-- Person inflection on the verb. -/
  | verbalAgreement
  /-- A zero. -/
  | zero
  deriving DecidableEq, Repr, Fintype

namespace AccessibilityLevel

/-- The scale orders the levels `fullNameMod < ⋯ < zero`, the order of the constructors. -/
instance : LinearOrder AccessibilityLevel :=
  LinearOrder.lift' AccessibilityLevel.ctorIdx (by decide)

/-! ### Features -/

/-- The head of a form class. -/
inductive Head where
  | name
  | description
  | demonstrative
  | pronoun
  | inflection
  | zero
  deriving DecidableEq, Repr, Fintype

/-- The head of a form class. -/
def head : AccessibilityLevel → Head
  | .fullNameMod | .fullName | .lastName | .firstName => .name
  | .longDefDescription | .shortDefDescription => .description
  | .distalDemMod | .proxDemMod | .distalDemNP | .proxDemNP | .distalDem | .proxDem =>
    .demonstrative
  | .stressedPronGesture | .stressedPron | .unstressedPron | .cliticizedPron => .pronoun
  | .verbalAgreement => .inflection
  | .zero => .zero

/-- A form carries a modifier, or is the long form of a description. -/
def modified : AccessibilityLevel → Prop
  | .fullNameMod | .longDefDescription | .distalDemMod | .proxDemMod => True
  | _ => False

/-- A form carries lexical content beyond its head, a noun or a name. -/
def lexical : AccessibilityLevel → Prop
  | .fullNameMod | .fullName | .lastName | .firstName | .longDefDescription
  | .shortDefDescription | .distalDemMod | .proxDemMod | .distalDemNP | .proxDemNP => True
  | _ => False

/-- A form is a full rather than a partial name. -/
def full : AccessibilityLevel → Prop
  | .fullNameMod | .fullName => True
  | _ => False

/-- The deictic content of a proximate demonstrative form is the participant sets containing the
speaker, and that of a distal form is the others. -/
def deixis : AccessibilityLevel → Option (Finset (Finset SpeechAct.Role))
  | .distalDemMod | .distalDemNP | .distalDem => some Person.first.participantSetsᶜ
  | .proxDemMod | .proxDemNP | .proxDem => some Person.first.participantSets
  | _ => none

/-- A form is a stressed pronoun. -/
def stressed : AccessibilityLevel → Prop
  | .stressedPronGesture | .stressedPron => True
  | _ => False

/-- A form is a bound pronominal, cliticized or verbal agreement. -/
def bound : AccessibilityLevel → Prop
  | .cliticizedPron | .verbalAgreement => True
  | _ => False

instance : DecidablePred modified := fun l ↦ by cases l <;> unfold modified <;> infer_instance
instance : DecidablePred lexical := fun l ↦ by cases l <;> unfold lexical <;> infer_instance
instance : DecidablePred full := fun l ↦ by cases l <;> unfold full <;> infer_instance
instance : DecidablePred stressed := fun l ↦ by cases l <;> unfold stressed <;> infer_instance
instance : DecidablePred bound := fun l ↦ by cases l <;> unfold bound <;> infer_instance

/-! ### The criteria -/

/-- A piece of the information a form incorporates. -/
inductive Information where
  /-- Grammatical features, the person, number and gender that any overt form marks. -/
  | grammatical
  /-- A lexical head, a noun or a name. -/
  | lexical
  /-- A modifier, or the long form of a description. -/
  | modifier
  /-- A full rather than a partial name. -/
  | fullName
  deriving DecidableEq, Repr, Fintype

/-- A form carries a piece of information. -/
def Information.CarriedBy : Information → AccessibilityLevel → Prop
  | .grammatical, l => l ≠ zero
  | .lexical, l => l.lexical
  | .modifier, l => l.modified
  | .fullName, l => l.full

instance (l : AccessibilityLevel) : DecidablePred (Information.CarriedBy · l) := fun i ↦ by
  cases i <;> unfold Information.CarriedBy <;> infer_instance

/-- The informativity of a form is the information it incorporates, one form being more
informative than another when it carries everything the other does. It separates a zero from a
pronoun, a pronoun or a bare demonstrative from a lexical phrase, a partial name from a full one
and an unmodified form from a modified one, and nothing else. -/
def informativity (l : AccessibilityLevel) : Finset Information :=
  Finset.univ.filter (Information.CarriedBy · l)

/-- How unequivocally a form picks out one referent among competitors. Names come close to
rigid designation, and the more varied a kind of name the less ambiguous it is. -/
inductive Rigidity where
  /-- A form that is not a name. -/
  | nonName
  /-- A first name. -/
  | firstName
  /-- A last name, less ambiguous than a first name, last names being the more varied. -/
  | lastName
  /-- A full name. -/
  | fullName
  deriving DecidableEq, Repr, Fintype

/-- `nonName < firstName < lastName < fullName`, the order of the constructors. -/
instance : LinearOrder Rigidity := LinearOrder.lift' Rigidity.ctorIdx (by decide)

/-- The rigidity of a form separates the names from the other forms and from one another. -/
def rigidity : AccessibilityLevel → Rigidity
  | .fullNameMod | .fullName => .fullName
  | .lastName => .lastName
  | .firstName => .firstName
  | _ => .nonName

/-- The phonological size of a form. -/
inductive Attenuation where
  /-- A lexical phrase is a name, a description or a demonstrative with a noun. -/
  | phrase
  /-- A stressed word is a stressed pronoun or a bare demonstrative. -/
  | stressedWord
  /-- An unstressed word. -/
  | unstressedWord
  /-- A clitic. -/
  | clitic
  /-- Verbal inflection. -/
  | inflection
  /-- Nothing. -/
  | zero
  deriving DecidableEq, Repr, Fintype

/-- The more attenuated a form, the higher it is in the order
`phrase < stressedWord < unstressedWord < clitic < inflection < zero` of the constructors. -/
instance : LinearOrder Attenuation := LinearOrder.lift' Attenuation.ctorIdx (by decide)

/-- The attenuation of a form is its phonological reduction, from a lexical phrase through bare
demonstratives and stressed, unstressed and cliticized pronouns and verbal agreement to a
zero. -/
def attenuation (l : AccessibilityLevel) : Attenuation :=
  match l.head with
  | .zero => .zero
  | .inflection => .inflection
  | .pronoun => if l.bound then .clitic else if l.stressed then .stressedWord else .unstressedWord
  | .demonstrative => if l.lexical then .phrase else .stressedWord
  | .name | .description => .phrase

/-- The three criteria jointly, in the product order: the lower of two forms is at least as
informative, as rigid and as unattenuated as the higher. -/
def criteria (l : AccessibilityLevel) : (Finset Information)ᵒᵈ × Rigidityᵒᵈ × Attenuation :=
  (OrderDual.toDual l.informativity, OrderDual.toDual l.rigidity, l.attenuation)

end AccessibilityLevel

end Discourse
