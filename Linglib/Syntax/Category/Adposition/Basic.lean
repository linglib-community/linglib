module

public import Linglib.Syntax.Case.Spatial
public import Linglib.Morphology.Morph
public import Linglib.Morphology.Word.Basic
public import Mathlib.Data.Finset.Image

/-!
# Adpositions

An adposition is a grammatical word that forms a phrase with a term it governs and marks, as a
case affix does, the relation of that term to the head of the phrase (Hagège's definition,
p. 8). Haspelmath groups case markers and adpositions together as *flags*, since they do the same
work and cannot be told apart consistently across languages. So an entry here records the
relations it marks as comparative case values, a set because adpositions are polysemous, beside
its exponent as morphs, the positions it takes relative to its term, and the complements it
takes. An adposition may occur without its term when the term is understood (Hagège p. 54,
*she stayed in*), and a particle such as Dutch *heen* occurs only without one.

## Main definitions

* `Adposition`: the entry.
* `Adposition.Linearization`, `Adposition.Complement`: positions and complement kinds.
* `Adposition.IsPreposition`, `IsPostposition`, `IsCircumposition`, `IsAmbiposition`: the
  position classes.
* `Adposition.Takes`, `IsIntransitive`, `IsTransitive`, `IsParticle`: valence.
* `Adposition.IsComplex`, `form`, `toWord`: the exponent.
* `Adposition.kinds`, `IsSpatial`: the types of case among the values marked.

## Main results

* `Adposition.isParticle_iff`: a particle takes no complement.
* `Adposition.isSpatial_iff`: a spatial adposition marks a value with a direction.

## Implementation notes

* The positions follow Dryer's WALS chapter 85 with circumpositions added. They are a set,
  since an ambiposition such as Dutch *op* is one lexeme preposed or postposed (Hagège
  pp. 114–116). A circumposition lists its pieces in surface order, the first before the term.
* The transitive and intransitive uses of one preposition are one entry, as in Huddleston and
  Pullum (p. 635).
* `functions` is `∅` where no comparative value fits, as for *despite*.
* The case an adposition governs on its complement (Corbett) is a fact about a language's own
  case values and is left to the fragments.

## References

* [hagege-2010]
* [haspelmath-2019]
* [huddleston-pullum-2002]
* [blake-2001]
* [corbett-2026]
* [dryer-2013-wals]
-/

@[expose] public section

open Morphology (Morph Word)

namespace Adposition

/-- The positions an adposition can take relative to the term it governs. -/
inductive Linearization where
  /-- A preposition precedes the term. -/
  | pre
  /-- A postposition follows the term. -/
  | post
  /-- A circumposition brackets the term, one piece on each side. -/
  | circum
  /-- An inposition occurs inside the term. -/
  | inposition
  deriving DecidableEq, Repr, Fintype

/-- The kinds of term an adposition governs. -/
inductive Complement where
  /-- A noun phrase, *in the garden*. -/
  | np
  /-- An adpositional phrase, Dutch *van boven de kast* 'from above the cupboard'. -/
  | pp
  /-- A clause, *after he had arrived*. -/
  | clause
  /-- An adjective phrase, Dutch *sinds kort* 'since recently'. -/
  | ap
  /-- A measure phrase, *for three hours*, *three days ago*. -/
  | measure
  /-- A subject with its predicate, the absolute construction, Dutch *met Jan ziek* 'with Jan
  ill'. -/
  | smallClause
  deriving DecidableEq, Repr, Fintype

end Adposition

/-- An adposition is its exponent, the positions it takes relative to the term it governs, the
comparative case values it marks, and the complements it takes, `none` for its use without
one. -/
structure Adposition where
  /-- The exponent, in surface order. -/
  morphs : List Morph
  /-- The positions relative to the governed term. -/
  linearization : Finset Adposition.Linearization
  /-- The comparative case values marked. -/
  functions : Finset Case
  /-- The complements taken; `none` is the use without a complement. -/
  complements : Finset (Option Adposition.Complement)
  deriving DecidableEq

namespace Adposition

variable (a : Adposition)

/-! ### The exponent -/

/-- The surface form of the exponent in boundary notation. -/
def form : String := Morph.surface a.morphs

instance : Repr Adposition := ⟨fun a _ ↦ a.form⟩

/-- A complex adposition has more than one piece, *in front of*, *van … af*. -/
def IsComplex : Prop := 1 < a.morphs.length

instance : Decidable a.IsComplex := inferInstanceAs (Decidable (_ < _))

/-- The adposition as a word, UD category `ADP`. -/
def toWord : Word := { form := a.form, cat := .ADP }

@[simp] theorem cat_toWord : a.toWord.cat = .ADP := rfl

/-! ### Position -/

/-- The adposition precedes its term. -/
def IsPreposition : Prop := .pre ∈ a.linearization

/-- The adposition follows its term. -/
def IsPostposition : Prop := .post ∈ a.linearization

/-- The adposition brackets its term. -/
def IsCircumposition : Prop := .circum ∈ a.linearization

/-- An ambiposition is preposed or postposed to its term. -/
def IsAmbiposition : Prop := a.IsPreposition ∧ a.IsPostposition

instance : Decidable a.IsPreposition := inferInstanceAs (Decidable (_ ∈ _))
instance : Decidable a.IsPostposition := inferInstanceAs (Decidable (_ ∈ _))
instance : Decidable a.IsCircumposition := inferInstanceAs (Decidable (_ ∈ _))
instance : Decidable a.IsAmbiposition := inferInstanceAs (Decidable (_ ∧ _))

/-! ### Valence -/

/-- The adposition takes a complement of kind `c`. -/
def Takes (c : Complement) : Prop := some c ∈ a.complements

/-- The adposition occurs without a complement. -/
def IsIntransitive : Prop := none ∈ a.complements

/-- The adposition takes some complement. -/
def IsTransitive : Prop := ∃ c, a.Takes c

/-- A particle occurs only without a complement. -/
def IsParticle : Prop := ∀ c ∈ a.complements, c = none

instance (c : Complement) : Decidable (a.Takes c) := inferInstanceAs (Decidable (_ ∈ _))
instance : Decidable a.IsIntransitive := inferInstanceAs (Decidable (_ ∈ _))
instance : Decidable a.IsTransitive := inferInstanceAs (Decidable (∃ c, a.Takes c))
instance : Decidable a.IsParticle := inferInstanceAs (Decidable (∀ c ∈ a.complements, c = none))

theorem isParticle_iff : a.IsParticle ↔ ¬ a.IsTransitive := by
  refine ⟨fun h ⟨c, hc⟩ ↦ Option.some_ne_none c (h _ hc), fun h c hc ↦ ?_⟩
  cases c with
  | none => rfl
  | some c => exact absurd ⟨c, hc⟩ h

/-! ### The values marked -/

/-- The types of case among the values the adposition marks. -/
def kinds : Finset Case.Kind := a.functions.image Case.kind

/-- A spatial adposition marks a spatial value. -/
def IsSpatial : Prop := .spatial ∈ a.kinds

instance : Decidable a.IsSpatial := inferInstanceAs (Decidable (_ ∈ _))

theorem isSpatial_iff : a.IsSpatial ↔ ∃ c ∈ a.functions, c.dirOf.isSome := by
  simp [IsSpatial, kinds, Case.kind_eq_spatial_iff]

end Adposition
