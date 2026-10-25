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
  | V     -- verb
  | N     -- noun
  | A     -- adjective
  | P     -- preposition
  | D     -- determiner
  | T     -- tense
  | C     -- complementizer
  | v     -- little v: the verbal categorizer, or the light verb above the root
  | n     -- nominal categorizer / gender (little-n, [marantz-2001]; Distributed Morphology)
  | a     -- adjectival categorizer (little-a, [panagiotidis-2015]; DegP complement)
  | Place -- locational head ([dendikken-2010]; PlaceP, F1 in adpositional EP)
  | Path  -- directional head ([dendikken-2010] [svenonius-2010]; PathP, F2 in adpositional EP)
  | Num   -- number ([ritter-1991]; NumP between nP and QP/DP)
  | Dem   -- demonstrative ([cinque-2005]; DemP above NumP in the nominal extended projection)
  | Q     -- quantity / classifier ([borer-2005]; QP between NumP and DP)
  | Voice -- Voice head ([kratzer-1996]; [schaefer-2008])
  | Appl  -- Applicative head ([pylkkanen-2008]; [cuervo-2003])
  | Foc   -- focus ([rizzi-1997] split-CP; hosts [FoC] feature, triggers A-bar movement)
  | Top   -- topic ([rizzi-1997] split-CP; hosts [G]/givenness, topic fronting)
  | Fin   -- finiteness ([rizzi-1997] split-CP; allocutive probe in Magahi/Galician)
  | SA    -- speech act head ([speas-tenny-2003]; hosts speaker/addressee)
  /-- The say/assertion layer ([major-2021], [krifka-2023], [moulton-2009]), embedding the
      content of a verbal or representational sign. Unlike the root illocutionary layer `SA`, it
      is clause-internal, in the embedded left periphery with Say > Foc > T, and requires no CP
      ([kiss-2023], [egressy-2026]). -/
  | Say
  | Force -- force ([rizzi-1997] split-CP; clause-typing [decl]/[interrog])
  | Neg   -- negation ([pollock-1989]; [zanuttini-1997]; hosts [±neg])
  | Mod   -- modality ([cinque-1999]; modal auxiliaries)
  | Rel   -- relative (cartographic left periphery, [rizzi-1997])
  | Pol   -- polarity ([laka-1990]; ΣP for affirmation/negation)
  | Asp   -- aspect ([cinque-1999]; inflectional, the aspect heads of `Cartography.Head`)
  | Evid  -- evidential ([cinque-1999]; inflectional, the evidential mood of `Cartography.Head`)
  /-- The nominalizer ([keine-2020]): the Hindi nominalized clause, a clause type distinct from
      CP. -/
  | Nmlz
  /-- The inherent-case shell ([newman-2024]): KP wraps DP for oblique or inherent case. -/
  | K
  deriving Repr, DecidableEq, Inhabited

/-- A selectional stack, consumed left to right. -/
abbrev SelStack := List Cat

end Minimalist
