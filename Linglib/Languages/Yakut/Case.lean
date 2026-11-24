module

public import Linglib.Morphology.Morph
public import Linglib.Syntax.Case.Function

/-!
# Yakut (Sakha) case

Sakha has eight cases: nominative, accusative, genitive, dative, ablative, instrumental,
comitative and partitive. There is no locative: the dative expresses location, and the old
locative suffix marks the partitive. The genitive is homophonous with the nominative except after a
third-person possessive suffix. [baker-vinokurova-2010]'s account of how the structural cases
are assigned is in `Studies/BakerVinokurova2010.lean`. The suffixes are [stachowski-menz-1998]'s
(p. 421), who count no genitive and add a comparative in *-TĀγAr*; the comitative is *-LĪn*, after
kinship terms *-nĀn*.

## Implementation notes

* Suffixes are written in Stachowski and Menz's notation, a capital for a consonant or vowel that
  assimilates to the stem.
* The genitive is recorded with the nominative's empty exponent; its form after a possessive
  suffix is not recorded.

## References

* [baker-vinokurova-2010]
* [stachowski-menz-1998]
-/

@[expose] public section

namespace Yakut

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
  /-- The ablative. -/
  | abl
  /-- The instrumental. -/
  | inst
  /-- The comitative. -/
  | com
  /-- The partitive. -/
  | part
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | gen => .gen
  | dat => .dat
  | abl => .abl
  | inst => .inst
  | com => .com
  | part => .part

/-- The functions a case marks: the dative has taken over the function of the old
locative ([stachowski-menz-1998] p. 421). -/
def Case.functions : Case → Finset _root_.Case.Function
  | dat => {.argument .R, .spatial none .place}
  | abl => {.spatial none .source}
  | c => c.label.functions

theorem Case.label_functions_inter_nonempty (c : Case) :
    (c.label.functions ∩ c.functions).Nonempty := by
  cases c <;> decide

/-- The suffixes of a case. -/
def Case.exponents : Case → List Morphology.Morph
  | nom | gen => []
  | acc => [.suff "(n)I"]
  | dat => [.suff "GA"]
  | abl => [.suff "(t)tAn"]
  | inst => [.suff "(I)nAn"]
  | com => [.suff "LĪn", .suff "nĀn"]
  | part => [.suff "TA"]

end Yakut
