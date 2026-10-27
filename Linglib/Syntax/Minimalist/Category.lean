/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Logic.Function.Basic

/-!
# Categories

The categories that label heads, those of the clausal spine and of the nominal and adpositional
extended projections, and the selectional stack, the categories a head selects, consumed left to
right. Each category belongs to one of four families, verbal, nominal, adjectival and
adpositional, each with its lexical head, V, N, A and P, and a functional head belongs to the
family of the lexical head it extends. The families carry the categorial features `[±V, ±N]`, and
the two binary features have four combinations, one for each family, so two categories share their
features exactly when they share their family.

## Main definitions

* `Minimalist.Cat`, `Minimalist.SelStack`: the categories and the selectional stack.
* `Minimalist.CatFamily`, `Minimalist.Cat.family`: the four families.
* `Minimalist.CatFamily.lexical`: the lexical head of a family.
* `Minimalist.CatFeatures`, `Minimalist.Cat.features`: the features `[±V, ±N]`, read off the
  family.

## Main results

* `Minimalist.CatFamily.features_bijective`: the features cross-classify the families.
* `Minimalist.Cat.features_eq_iff`: two categories share their features exactly when they share
  their family.

## Implementation notes

Chomsky's features first classified the noun, the verb and the adjective; the fourth combination,
`[−V, −N]`, was given to the adposition afterwards [baker-2003].

## References

* [chomsky-1970]
* [baker-2003]
* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist

/-- The categories that label heads, those of the clausal spine and of the nominal and
adpositional extended projections. -/
inductive Cat where
  /-- The verb. -/
  | V
  /-- The noun. -/
  | N
  /-- The adjective. -/
  | A
  /-- The adposition. -/
  | P
  /-- The determiner. -/
  | D
  /-- Tense. -/
  | T
  /-- The complementizer. -/
  | C
  /-- Little v, the verbal categorizer or the light verb above the root. -/
  | v
  /-- Little n, the nominal categorizer ([marantz-2001]), also the head that bears gender. -/
  | n
  /-- Little a, the adjectival categorizer ([panagiotidis-2015]). -/
  | a
  /-- The locational head of the adposition ([dendikken-2010]). -/
  | Place
  /-- The directional head of the adposition, above Place ([dendikken-2010], [svenonius-2010]). -/
  | Path
  /-- Number ([ritter-1991]), Borer's counting head, above the dividing head `Q`
  ([borer-2005]). -/
  | Num
  /-- The demonstrative, above number ([cinque-2005]). -/
  | Dem
  /-- Borer's dividing head, the classifier position, below `Num` ([borer-2005]). -/
  | Q
  /-- Voice, which introduces the external argument ([kratzer-1996], [schaefer-2008]). -/
  | Voice
  /-- The applicative head ([pylkkanen-2008], [cuervo-2003]). -/
  | Appl
  /-- Focus, in Rizzi's split complementizer system ([rizzi-1997]). -/
  | Foc
  /-- Topic, in Rizzi's split complementizer system ([rizzi-1997]). -/
  | Top
  /-- Finiteness, the lowest head of Rizzi's split complementizer system ([rizzi-1997]). -/
  | Fin
  /-- The speech-act head, which hosts the speaker and the addressee ([speas-tenny-2003]). -/
  | SA
  /-- The say/assertion layer ([major-2021], [krifka-2023], [moulton-2009]), embedding the
  content of a verbal or representational sign. Unlike the root illocutionary layer `SA`, it is
  clause-internal, in the embedded left periphery with Say > Foc > T, and requires no CP
  ([kiss-2023], [egressy-2026]). -/
  | Say
  /-- Force, the clause-typing head at the top of Rizzi's split complementizer system
  ([rizzi-1997]). -/
  | Force
  /-- Negation ([pollock-1989], [zanuttini-1997]). -/
  | Neg
  /-- Modality ([cinque-1999]). -/
  | Mod
  /-- Polarity, Laka's Σ, for affirmation and negation ([laka-1990]). -/
  | Pol
  /-- Outer aspect, inflectional and above Voice ([cinque-1999]). -/
  | Asp
  /-- Inner aspect ([travis-2010]): Aktionsart in the v shell, below Voice. -/
  | InnerAsp
  /-- Evidential mood, inflectional ([cinque-1999]). -/
  | Evid
  /-- Mood ([cinque-1999]): the speech-act, evaluative and irrealis moods, inflectional. -/
  | Mood
  /-- The nominalizer ([keine-2020]): the Hindi nominalized clause, a clause type distinct from
  CP. -/
  | Nmlz
  /-- The inherent-case shell ([newman-2024]): KP wraps DP for oblique or inherent case. -/
  | K
  deriving Repr, DecidableEq, Inhabited

/-- A selectional stack, consumed left to right. -/
abbrev SelStack := List Cat

/-! ### Families -/

/-- The four families of extended projections, each anchored by a lexical category. -/
inductive CatFamily
  | verbal
  | nominal
  | adjectival
  | adpositional
  deriving DecidableEq, Repr

/-- The lexical head of a family, at the foot of its extended projections. -/
def CatFamily.lexical : CatFamily → Cat
  | .verbal => .V
  | .nominal => .N
  | .adjectival => .A
  | .adpositional => .P

/-- The family of a category, the extended projection it belongs to. -/
def Cat.family : Cat → CatFamily
  | .V | .v | .Voice | .Appl | .T | .Foc | .Top | .Fin | .C | .SA | .Say
  | .Force | .Neg | .Mod | .Mood | .Pol | .Asp | .InnerAsp | .Evid | .Nmlz => .verbal
  | .N | .n | .Num | .Dem | .Q | .D | .K => .nominal
  | .A | .a => .adjectival
  | .P | .Place | .Path => .adpositional

@[simp] theorem CatFamily.family_lexical (f : CatFamily) : f.lexical.family = f := by
  cases f <;> rfl

/-! ### Categorial features -/

/-- The categorial features `[±V, ±N]`, which cross-classify the four lexical categories: V is
`[+V, −N]`, N is `[−V, +N]`, A is `[+V, +N]` and P is `[−V, −N]`. -/
structure CatFeatures where
  plusV : Bool
  plusN : Bool
  deriving DecidableEq, Repr

/-- The features of a family are those of its lexical head. -/
def CatFamily.features : CatFamily → CatFeatures
  | .verbal => ⟨true, false⟩
  | .nominal => ⟨false, true⟩
  | .adjectival => ⟨true, true⟩
  | .adpositional => ⟨false, false⟩

/-- Each of the four combinations of the two features is the features of exactly one family. -/
theorem CatFamily.features_bijective : Function.Bijective CatFamily.features :=
  ⟨fun a b h ↦ by cases a <;> cases b <;> simp_all [features], fun
    | ⟨true, false⟩ => ⟨.verbal, rfl⟩
    | ⟨false, true⟩ => ⟨.nominal, rfl⟩
    | ⟨true, true⟩ => ⟨.adjectival, rfl⟩
    | ⟨false, false⟩ => ⟨.adpositional, rfl⟩⟩

/-- The features of a category are those of its family, so that every functional head inherits
the features of its lexical head. -/
def Cat.features (c : Cat) : CatFeatures := c.family.features

theorem Cat.features_eq_iff {c d : Cat} : c.features = d.features ↔ c.family = d.family :=
  CatFamily.features_bijective.injective.eq_iff

end Minimalist
