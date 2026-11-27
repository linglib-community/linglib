/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Morph
public import Linglib.Morphology.Word.Basic
public import Linglib.Syntax.Feature.Case.Function
public import Mathlib.Data.Fin.VecNotation

/-!
# Coordinators

A coordinator is a word or clitic that links the coordinands of a coordinate construction, such
as *and*, *or*, *but* and *nor*. This file defines its lexical record, the morph, which says
whether the coordinator is a free word or a bound clitic or affix, the gloss and the semantic
type, and the relations that give the other uses its form has. What a coordinator denotes, an
operation on the set of coordinands that its semantic type fixes, is `Coordinator.denote` in
`Semantics/Coordinator.lean`.

## Main definitions

* `Coordinator.Role`: the semantic type of a coordinator.
* `Coordinator`: the morph, gloss and semantic type of a coordinator.
* `Coordinator.Pattern`: the sides of each coordinand on which the coordinators of a binary
  coordination stand.
* `Coordinator.Correlative`: a pair of correlative coordinators with the single coordinator
  of the plain construction.
* `Coordinator.IsAlsoComitative`: the coordinator's form is a form of a comitative marker, 'and'
  is 'with'.

## Implementation notes

* The other uses of a coordinator's form are relations to entries of other categories, not fields:
  a comitative use to a comitative marker of the language, an adposition or a case with its
  exponents, and an additive or a quantifier use to an additive particle or an indeterminate
  quantifier of the language whose morph is the coordinator's. Whether the coordinator and the
  particle are one item is for the accounts to say.
* Analyses that divide the conjunctive coordinators further, such as the two conjunction heads
  of Mitrović and Sauerland, classify the entries in their own studies.

## References

* [haspelmath-1997]
* [haspelmath-2007]
* [mitrovic-sauerland-2016]
* [stassen-2000]
-/

@[expose] public section

namespace Coordinator

/-- A coordinator's semantic type is conjunction, disjunction, adversative or negative
coordination. -/
inductive Role where
  /-- Conjunction, English *and*. -/
  | conjunctive
  /-- Disjunction, English *or*. -/
  | disjunctive
  /-- Adversative coordination, English *but*. -/
  | adversative
  /-- Negative coordination, English *nor*, Latin *neque*. -/
  | negative
  deriving DecidableEq, Repr

end Coordinator

/-- A coordinator of a language. Its denotation is not stored, since its semantic type fixes it,
`Coordinator.denote`. -/
structure Coordinator where
  /-- The form, a free word or a clitic or affix bound on one side of its host. -/
  morph : Morphology.Morph
  /-- The gloss. -/
  gloss : String
  /-- The semantic type. -/
  role : Coordinator.Role
  deriving DecidableEq, Repr

/-- The pattern of a binary coordination gives each coordinand the sides on which a coordinator
stands by it, none when it is bare, so that A co-B is `![∅, {.before}]` and A-co B-co is
`![{.after}, {.after}]`: the number of coordinators and their positions, the two parameters by
which [stassen-2000] and [haspelmath-2007] classify coordinate constructions. Patterns are ordered
coordinand by coordinand, and the join of two is the construction that uses the coordinators of
both, as Hungarian *A is és B is* joins *A és B* and *A is B is*. -/
abbrev Coordinator.Pattern := Fin 2 → Finset Morphology.Morph.Side

/-- An emphatic coordination with correlative coordinators, English *both … and*, records the
coordinators of the two coordinands and the single coordinator of the plain construction. -/
structure Coordinator.Correlative where
  /-- The form on the first coordinand. -/
  first : List Morphology.Morph
  /-- The form on the second coordinand. -/
  second : List Morphology.Morph
  /-- The coordinator of the plain construction. -/
  single : Coordinator
  deriving DecidableEq, Repr

namespace Coordinator

variable (c : Coordinator)

/-- `c.toWord` is the coordinator as a word, of UD category `CCONJ`, its form in boundary
notation. -/
def toWord : Morphology.Word := { form := toString c.morph, cat := .CCONJ }

/-- A coordinator is also comitative when its morph is one of the forms `ms` of a marker whose
functions `fs` include the comitative, so that 'and' is 'with', [stassen-2000]'s lexical
identity of the coordinator with the comitative marker. The marker is an adposition, with its
morphs and functions, or a case of the language, with its exponents and functions. -/
def IsAlsoComitative (ms : List Morphology.Morph) (fs : Finset Case.Function) : Prop :=
  c.morph ∈ ms ∧ .comitative ∈ fs

instance (ms : List Morphology.Morph) (fs : Finset Case.Function) :
    Decidable (c.IsAlsoComitative ms fs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Patterns -/

namespace Pattern

variable (p : Pattern)

/-- The syndesis of a pattern is its number of coordinators, none in asyndetic, one in
monosyndetic and two in bisyndetic coordination. -/
def syndesis : ℕ := (p 0).card + (p 1).card

end Pattern

end Coordinator
