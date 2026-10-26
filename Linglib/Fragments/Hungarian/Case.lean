module

public import Linglib.Syntax.Case.Spatial

/-!
# Hungarian case

Hungarian marks case by agglutinative suffix. Kenesei, Vago and Fenyvesi list eighteen cases:
the nominative, the accusative *-t*, the dative *-nak ~ -nek*, the instrumental *-val ~ -vel*,
the causal *-ért*, the essive *-ul ~ -ül*, the essive-formal *-ként*, the terminative *-ig*, the
translative *-vá ~ -vé*, and the nine local cases, which form a matrix of three regions,
interior, exterior and near, by three directions, motion toward, rest and motion away: the
illative *-ba ~ -be*, inessive *-ban ~ -ben* and elative *-ból ~ -ből*, the sublative *-ra ~
-re*, superessive *-n* and delative *-ról ~ -ről*, and the allative *-hoz*, adessive *-nál ~
-nél* and ablative *-tól ~ -től*. Rounds adds the less productive temporal *-kor*, distributive
*-nként*, distributive-temporal *-nta* and sociative *-stul ~ -stül*. There is no genitive: the
possessor within the noun phrase is nominative or dative, and both grammars gloss *-nak ~ -nek*
as a dative throughout, the reading under which Blake and Caha take Hungarian's missing
genitive as a superficial exception to the case hierarchy.

## Main definitions

* `Hungarian.Case`, `Hungarian.Case.label`: the cases with a comparative label, and that label.

## Main results

* `Hungarian.Case.cells_image_label`: the local cases fill the matrix of three regions by three
  directions.

## Implementation notes

The essive-formal, the distributive, the distributive-temporal and the sociative have no
comparative label and are left out; the instrumental *-val ~ -vel* also expresses
accompaniment, and no separate comitative is recorded.

## References

* [kenesei-vago-fenyvesi-1998]
* [rounds-2001]
* [caha-2008]
-/

@[expose] public section

namespace Hungarian

/-- The cases with a comparative label: the three grammatical cases, the nine local cases, the
instrumental, the causal, the essive, the translative, the terminative and the temporal. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  /-- The dative. -/
  | dat
  /-- The inessive. -/
  | ine
  /-- The adessive. -/
  | ade
  /-- The superessive. -/
  | sup
  /-- The elative. -/
  | ela
  /-- The ablative. -/
  | abl
  /-- The delative. -/
  | del
  /-- The illative. -/
  | ill
  /-- The allative. -/
  | all
  /-- The sublative. -/
  | sub
  /-- The instrumental. -/
  | inst
  /-- The causal. -/
  | caus
  /-- The essive. -/
  | ess
  /-- The translative. -/
  | transl
  /-- The terminative. -/
  | ter
  /-- The temporal. -/
  | tem
  deriving DecidableEq, Fintype, Repr

/-- The comparative value a case is named for. -/
def Case.label : Case → _root_.Case
  | nom => .nom
  | acc => .acc
  | dat => .dat
  | ine => .ine
  | ade => .ade
  | sup => .sup
  | ela => .ela
  | abl => .abl
  | del => .del
  | ill => .ill
  | all => .all
  | sub => .sub
  | inst => .inst
  | caus => .caus
  | ess => .ess
  | transl => .transl
  | ter => .ter
  | tem => .tem

/-- The nine local cases are the matrix of three regions by three directions. -/
theorem Case.cells_image_label : _root_.Case.cells (Finset.univ.image Case.label) =
    (.univ : Finset Spatial.Localization) ×ˢ
      ({.place, .source, .goal} : Finset Spatial.Path.Direction) := by
  decide

end Hungarian
