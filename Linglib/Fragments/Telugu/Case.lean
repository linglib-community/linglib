module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Case.Basic

/-!
# Telugu case

Telugu marks four cases on the noun by suffix and the other relations by postposition. The
nominative is the bare stem and the genitive the oblique stem, neither with a suffix; the
accusative suffix is *-ni* and the dative *-ki*, each also heard with *-u* for *-i* except after
an *i*. The oblique stem carries the accusative and dative suffixes and the postpositions alike,
among them *lō* 'in' and *nunci* 'from' (`Telugu.Adpositions`). Krishnamurti and Gwynn count the
case suffixes among the postpositions that only occur bound to the stem (§§9.12–9.14), and Aitha
separates them, the postpositions standing outside the noun's prosodic word. The forms
are those of the paradigms of *illu* 'house' and *samudram* 'ocean' that Aitha reproduces from
Krishnamurti and Gwynn's grammar; the oblique stem is the matter of `Studies/Aitha2026.lean`.

## Main definitions

* `Telugu.Case`, `Telugu.Case.exponents`: the four cases, and the suffixes of the two that have
  one.

## References

* [aitha-2026]
* [krishnamurti-gwynn-1985]
* [kolichala-2026]
-/

@[expose] public section

namespace Telugu

/-! ### Cases -/

/-- The four cases. -/
inductive Case where
  /-- The nominative, the bare stem. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The genitive, the oblique stem. -/
  | gen
  /-- The dative. -/
  | dat
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for. -/
def label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat

/-- The suffix of a case, inside the noun's prosodic word, is *-ni* for the accusative, also
*-nu* except after an *i*, and *-ki* for the dative, also *-ku* except after an *i*. The nominative
and the genitive have none. -/
def exponents : Case → List Morphology.Morph
  | nom | gen => []
  | acc => [.suff "ni", .suff "nu"]
  | dat => [.suff "ki", .suff "ku"]

end Case

end Telugu
