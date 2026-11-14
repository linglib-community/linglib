module

public import Linglib.Syntax.Case.Spatial

/-!
# Finnish case

Karlsson's table of cases lists fifteen, with their endings in the singular: the nominative,
which has none, the genitive -n, the accusative -t, which only the personal pronouns and *kuka*
'who' take, as in *häne-t* 'him, her', the partitive -A, the six local cases, and the essive
-nA, the translative -ksi, the comitative -ine, the abessive -ttA and the instructive -n. The
local cases are structured along two dimensions, location, inside or outside, and direction,
static, away from or towards. The internal cases are the inessive -ssA 'in', the elative -stA
'out of' and the illative -Vn 'into', and the external cases the adessive -llA 'on', the ablative
-ltA 'off' and the allative -lle 'onto'.

Finnish has no surface series, which Hungarian has (`Hungarian.Case`), and no dative, and the
external cases do the work of both: the adessive, ablative and allative also mean on, off and
towards a surface, and the allative marks the recipient, as in *minu-lle* 'to me'. The adessive
also expresses the instrument. The instructive, a case of manner, means, instrument, location or
time found mostly in fixed plural expressions, is labelled the instrumental; its singular ending
is the genitive's, as in *jala-n* 'on foot' beside *auto-n* 'of a car'.

## Main definitions

* `Finnish.Case`: the fifteen cases, in the order of Karlsson's table.
* `Finnish.Case.label`, `Finnish.Case.functions`: the comparative value each case is named for,
  and the values it expresses.

## Main results

* `Finnish.Case.isSome_spatialDecomp_label_iff`: the local cases are those whose label decomposes
  into a localization and a direction.
* `Finnish.Case.cells_image_label`, `Finnish.Case.cells_biUnion_functions`: the labels fill the
  interior and exterior localizations of the table, and the functions every localization.

## Implementation notes

`functions` leaves out time, which Karlsson gives most of the cases, and the owner the adessive
marks, as in *minu-lla on* 'I have', which has no comparative value. The endings, spelled in
segments, are in `Finnish.Declension`.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Finnish

/-- The fifteen cases, in the order of Karlsson's table. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The genitive. -/
  | gen
  /-- The accusative. -/
  | acc
  /-- The partitive. -/
  | part
  /-- The inessive. -/
  | ine
  /-- The elative. -/
  | ela
  /-- The illative. -/
  | ill
  /-- The adessive. -/
  | ade
  /-- The ablative. -/
  | abl
  /-- The allative. -/
  | all
  /-- The essive. -/
  | ess
  /-- The translative. -/
  | transl
  /-- The comitative. -/
  | com
  /-- The abessive. -/
  | abess
  /-- The instructive, of manner and means. -/
  | instr
  deriving DecidableEq, Fintype, Repr

namespace Case

/-- The comparative value a case is named for, the instrumental for the instructive. -/
def label : Case → _root_.Case
  | nom => .nom
  | gen => .gen
  | acc => .acc
  | part => .part
  | ine => .ine
  | ela => .ela
  | ill => .ill
  | ade => .ade
  | abl => .abl
  | all => .all
  | ess => .ess
  | transl => .transl
  | com => .com
  | abess => .abess
  | instr => .inst

/-- The comparative values a case expresses: the external cases also express the surface
relations ([karlsson-2017] pp. 243, 247, 250), the adessive the instrument (p. 243), the allative
the recipient (p. 250) and the instructive location (p. 264). -/
def functions : Case → Finset _root_.Case
  | ade => {.ade, .sup, .inst}
  | abl => {.abl, .del}
  | all => {.all, .sub, .dat}
  | instr => {.inst, .loc}
  | c => {c.label}

theorem label_mem_functions (c : Case) : c.label ∈ c.functions := by
  cases c <;> decide

/-- The local cases are those whose label decomposes into a localization and a direction. -/
theorem isSome_spatialDecomp_label_iff (c : Case) :
    c.label.spatialDecomp.isSome ↔ c.label.kind = .spatial := by
  cases c <;> decide

open _root_.Case (cells)
open Spatial (Localization)
open Spatial.Path (Direction)

/-- The local cases are the internal and external cases, each static, away from or towards
([karlsson-2017] p. 228). -/
theorem cells_image_label : cells (Finset.univ.image label) =
    ({.interior, .exterior} : Finset Localization) ×ˢ
      ({.place, .source, .goal} : Finset Direction) := by
  decide

/-- The external cases also express the surface relations, so that the functions of the Finnish
cases fill every localization. -/
theorem cells_biUnion_functions : cells (Finset.univ.biUnion functions) =
    (.univ : Finset Localization) ×ˢ ({.place, .source, .goal} : Finset Direction) := by
  decide

end Case

end Finnish
