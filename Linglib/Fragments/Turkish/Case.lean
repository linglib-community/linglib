module

public import Linglib.Syntax.Case.Basic

/-!
# Turkish case

This file defines the cases of Turkish. Göksel and Kerslake list five case suffixes, the
accusative *-(y)I*, the dative *-(y)A*, the locative *-DA*, the ablative *-DAn* and the genitive
*-(n)In*, and Blake's table adds the unmarked nominative for a system of six cases. The
suffixes are the case exponents of the nominal in `Morphotactics.lean`, which maps each to the
case it realizes and proves that they realize every case but the nominative, once each. The
comitative and instrumental *-(y)lA* is not a case suffix in the grammar's analysis but an
unstressable marker that forms postpositional phrases, `Turkish.Adpositions.ile`.

## Main definitions

* `Turkish.Case`, `Turkish.Case.label`: the six cases, and the comparative value each is named for

## References

* [A. Göksel and C. Kerslake, *Turkish: A Comprehensive Grammar* (2005)][goksel-kerslake-2005]
* [B. J. Blake, *Case* (1994)][blake-1994]
-/

@[expose] public section

namespace Turkish

/-- The six cases. -/
inductive Case where
  /-- The nominative, unmarked. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The dative. -/
  | dat
  /-- The locative. -/
  | loc
  /-- The ablative. -/
  | abl
  /-- The genitive. -/
  | gen
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | dat => .dat
  | loc => .loc
  | abl => .abl
  | gen => .gen

end Turkish
