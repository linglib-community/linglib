module

public import Linglib.Syntax.Case.Function

/-!
# Mongolian case

Mongolian (Khalkha and Chakhar) has seven cases: nominative, accusative, genitive, dative,
ablative, instrumental and comitative. The inventory has no dedicated locative: the dative
expresses location, as in *Gowi-d* 'in the Gobi' ([gong-2026]), and so do postpositions.
[gong-2022]'s account of how the structural cases are assigned is in `Studies/Gong2022.lean`.

## References

* [gong-2022]
* [gong-2026]
* [creissels-2009]
-/

@[expose] public section

namespace Mongolian

/-- The seven cases. -/
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

/-- The functions a case marks: the dative also expresses location, and not the goal of motion,
which has a marker of its own ([creissels-2009]). -/
def Case.functions : Case → Finset _root_.Case.Function
  | dat => {.argument .R, .spatial none .place}
  | abl => {.spatial none .source}
  | c => c.label.functions

theorem Case.label_functions_inter_nonempty (c : Case) :
    (c.label.functions ∩ c.functions).Nonempty := by
  cases c <;> decide

end Mongolian
