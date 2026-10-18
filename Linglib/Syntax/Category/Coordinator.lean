module

public import Linglib.Morphology.Morph
public import Linglib.Morphology.Word.Basic
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Category.Particle.Additive

/-!
# Coordinators

A coordinator is a word or clitic that links the coordinands of a coordinate construction, such
as *and*, *or*, *but* and *nor*. This file defines its lexical record, the morph, which says
whether the coordinator is a free word or a bound clitic or affix, the gloss and the semantic
type, and the relations that give the other uses its form has. What a coordinator denotes, an
operation on the set of coordinands that its semantic type fixes, is `Coordinator.denote` in
`Semantics/Composition/Coordinator.lean`.

## Main definitions

* `Coordinator.Role`: the semantic type of a coordinator.
* `Coordinator`: the morph, gloss and semantic type of a coordinator.
* `Coordinator.Correlative`: a pair of correlative coordinators with the single coordinator
  of the plain construction.
* `Coordinator.IsAlsoComitative`: the coordinator's form is a form of a comitative marker, 'and'
  is 'with'.
* `Coordinator.IsAlsoAdditive`: the coordinator's form is that of an additive particle, 'and' is
  'too'.

## Implementation notes

* The other uses of a coordinator's form are relations to entries of other categories, not fields:
  a comitative use to a comitative marker of the language, an adposition or a case with its
  exponents, an additive use to an `AdditiveParticle`, and a quantifier use to an
  `IndeterminateQuantifier` of the language whose particle is the coordinator.
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
case values `fs` include the comitative, so that 'and' is 'with', [stassen-2000]'s lexical
identity of the coordinator with the comitative marker. The marker is an adposition, with its
morphs and functions, or a case of the language, with its exponents and functions. -/
def IsAlsoComitative (ms : List Morphology.Morph) (fs : Finset Case) : Prop :=
  c.morph ∈ ms ∧ .com ∈ fs

instance (ms : List Morphology.Morph) (fs : Finset Case) :
    Decidable (c.IsAlsoComitative ms fs) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A coordinator is also additive when its morph is that of an additive particle `a`, so that
'and' is 'too', the identity of the two that [haspelmath-1997] notes and on which
[mitrovic-sauerland-2016] build. -/
def IsAlsoAdditive (a : AdditiveParticle) : Prop := c.morph = a.morph

instance (a : AdditiveParticle) : Decidable (c.IsAlsoAdditive a) :=
  inferInstanceAs (Decidable (_ = _))

end Coordinator
