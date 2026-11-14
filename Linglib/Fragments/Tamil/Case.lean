module

public import Linglib.Syntax.Case.Basic

/-!
# Tamil case

Tamil has eight cases, the seven of Classical Armenian on Blake's inflectional case hierarchy,
the nominative, accusative, genitive, dative, locative, ablative and instrumental, and the
comitative, which Dravidian grammars call the sociative. The oblique cases of some singular
nouns are suffixed to an oblique stem distinct from the nominative: *maram* 'tree' has the
accusative *maratt-ai* and the dative *maratt-ukku*, and the stem-forming element never
appears without a following case suffix, so that the nominative stands off from the other
cases. Blake takes Tamil as the eight-case stage of his hierarchy (`Studies/Blake1994.lean`).

## Main definitions

* `Tamil.Case`, `Tamil.Case.label`: the eight cases, and the comparative value each is named for.

## References

* [blake-1994]
-/

@[expose] public section

namespace Tamil

/-- The eight cases. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The genitive. -/
  | gen
  /-- The dative. -/
  | dat
  /-- The locative. -/
  | loc
  /-- The ablative. -/
  | abl
  /-- The instrumental. -/
  | inst
  /-- The comitative. -/
  | com
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat
  | loc => .loc
  | abl => .abl
  | inst => .inst
  | com => .com

end Tamil
