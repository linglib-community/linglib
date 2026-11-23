/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.DeriveFintype

/-!
# Categories

The categories that label heads, those of the clausal spine and of the nominal and adpositional
extended projections, and the selectional stack, the categories a head selects, consumed left to
right. Each category belongs to one of four families, verbal, nominal, adjectival and
adpositional, each with its lexical head, V, N, A and P, and a functional head belongs to the
family of the lexical head it extends. There are two categorial features, `N` and `V`, and a family
is specified by the set of them it is positive for: `{V}` for the verbal family, `{N}` for the
nominal, both for the adjectival and neither for the adpositional. The four sets are the four
families, so two categories share their features exactly when they share their family.

## Main definitions

* `Minimalist.Cat`: the categories.
* `Minimalist.Cat.IsCategorizer`: the categorizers n, v and a.
* `Minimalist.CatFamily`, `Minimalist.Cat.family`: the four families.
* `Minimalist.CatFamily.lexical`: the lexical head of a family.
* `Minimalist.CategorialFeature`: the categorial features `N` and `V`.
* `Minimalist.CatFamily.features`, `Minimalist.Cat.features`: the features a family, and a
  category of it, is positive for.
* `Minimalist.CatFamily.featuresEquiv`: the families as the sets of categorial features.

## Main results

* `Minimalist.CatFamily.features_bijective`: the features cross-classify the families.
* `Minimalist.Cat.features_eq_iff`: two categories share their features exactly when they share
  their family.

## Implementation notes

A specification `[±V, ±N]` is the set of features it is positive for, so that the class `[+N]` is
the families whose set contains `N` and `[−N]` those whose set does not. Chomsky's features first
classified the noun, the verb and the adjective; the fourth combination,
`[−V, −N]`, was given to the adposition afterwards [baker-2003].

## References

* [chomsky-1970]
* [baker-2003]
* [chomsky-2013]
* [marantz-2001]
* [pietraszko-2019]
* [arregi-pietraszko-2021]
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
  /-- The possessive head, which introduces a possessor inside the noun phrase, below number
  ([myler-2016], [thoms-etal-2026]). -/
  | Poss
  /-- The demonstrative, above number ([cinque-2005]). -/
  | Dem
  /-- Borer's dividing head, the classifier position, below `Num` ([borer-2005]). -/
  | Q
  /-- Voice, which introduces the external argument ([kratzer-1996], [schaefer-2008]). -/
  | Voice
  /-- The applicative head ([pylkkanen-2008], [cuervo-2003]). -/
  | Appl
  /-- The directional auxiliary of the Mayan clause, above Voice
  ([elkins-torrence-brown-2026]). -/
  | Dir
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
  /-- The associative linker, above the determiner, which introduces a possessor or a relative
  clause modifying a noun in Bantu ([pietraszko-2019], [arregi-pietraszko-2021]). -/
  | Lnk
  deriving Repr, DecidableEq, Inhabited

/-- The categorizers, little n, v and a, one of which merges with every root ([marantz-2001]). -/
def Cat.IsCategorizer : Cat → Prop
  | .n | .v | .a => True
  | _ => False

instance : DecidablePred Cat.IsCategorizer := fun c ↦ by
  cases c <;> unfold Cat.IsCategorizer <;> infer_instance

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
  | .V | .v | .Voice | .Appl | .Dir | .T | .Foc | .Top | .Fin | .C | .SA | .Say
  | .Force | .Neg | .Mod | .Mood | .Pol | .Asp | .InnerAsp | .Evid | .Nmlz => .verbal
  | .N | .n | .Poss | .Num | .Dem | .Q | .D | .K | .Lnk => .nominal
  | .A | .a => .adjectival
  | .P | .Place | .Path => .adpositional

@[simp] theorem CatFamily.family_lexical (f : CatFamily) : f.lexical.family = f := by
  cases f <;> rfl

/-! ### Categorial features -/

/-- The categorial features. -/
inductive CategorialFeature where
  | N
  | V
  deriving DecidableEq, Repr, Fintype

/-- The categorial features a family is positive for: V is `[+V, −N]`, N is `[−V, +N]`, A is
`[+V, +N]` and P is `[−V, −N]`. -/
def CatFamily.features : CatFamily → Finset CategorialFeature
  | .verbal => {.V}
  | .nominal => {.N}
  | .adjectival => {.N, .V}
  | .adpositional => ∅

/-- The families are the sets of categorial features. -/
def CatFamily.featuresEquiv : CatFamily ≃ Finset CategorialFeature where
  toFun := features
  invFun s :=
    if .N ∈ s then (if .V ∈ s then .adjectival else .nominal)
    else if .V ∈ s then .verbal else .adpositional
  left_inv f := by cases f <;> simp [features]
  right_inv s := by
    ext x
    by_cases hN : CategorialFeature.N ∈ s <;> by_cases hV : CategorialFeature.V ∈ s <;>
      cases x <;> simp [features, hN, hV]

@[simp] theorem CatFamily.coe_featuresEquiv : ⇑CatFamily.featuresEquiv = CatFamily.features := rfl

/-- Each set of categorial features is the features of exactly one family. -/
theorem CatFamily.features_bijective : Function.Bijective CatFamily.features :=
  CatFamily.featuresEquiv.bijective

/-- The features of a category are those of its family, so that every functional head inherits
the features of its lexical head. -/
def Cat.features (c : Cat) : Finset CategorialFeature := c.family.features

theorem Cat.features_eq_iff {c d : Cat} : c.features = d.features ↔ c.family = d.family :=
  CatFamily.features_bijective.injective.eq_iff

end Minimalist
