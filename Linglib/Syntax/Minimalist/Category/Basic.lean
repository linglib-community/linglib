/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

/-!
# Categories

The categorial features that label heads, the categories of the clausal spine and of the nominal
and adpositional extended projections, and the selectional stack, the categories a head selects,
consumed left to right.

## Main definitions

* `Minimalist.Cat`, `Minimalist.SelStack`

## References

* [chomsky-2013]
-/

@[expose] public section

namespace Minimalist

/-- The categorial features, the head categories of the clausal spine and the nominal and
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
  /-- Borer's dividing head, the classifier position, between little n and `Num`
  ([borer-2005]). -/
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

end Minimalist
