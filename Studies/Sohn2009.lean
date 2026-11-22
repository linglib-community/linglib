module

public import Mathlib.Data.Finset.Lattice.Basic
public import Linglib.Fragments.Korean.Clause
public import Linglib.Syntax.Clause.Linking

/-!
# Sohn (2009): The Semantics of Clause Linking in Korean

Korean links clauses chiefly by a conjunctive ender on the predicate of the non-main clause, which
precedes the main clause, and the chapter sorts the enders by Dixon's semantic types of clause
linking. `table` records, for the conjunctive suffixes of the Korean Fragment, the kinds of
linking the chapter's summary table gives each and whether the clause it marks is the focal or
the supporting clause of the linking. A non-main clause is the supporting clause in every kind
but three: in purpose linking it is the focal clause, and unordered addition and disjunction do
not tell the two apart (`role_eq_focal_iff`, `role_isSome_iff`). One ender can mark several
kinds, *-eoseo* five of them (`linkings_eoseo`), and *-dorok* marks a supporting clause as 'until'
and a focal clause as 'so that'.

## Implementation notes

The chapter writes the enders in Yale romanization: *-ko*, *-kose*, *-(u)myense*, *-ese ~ -ase*,
*-(u)myen*, *-ciman*, *-(u)na*, *-eto ~ -ato*, *-tolok*, *-(u)nikka*, *-(u)ni*, *-(n)untey*,
*-(u)lyeko*, *-(u)le*, *-taka*, *-ca(maca)*, *-kena*, *-tunci*. Its ways and means, a subtype of
manner it adds for *-ese*, is classed with real manner. The rows are those of the summary table;
the further uses the chapter lists in prose, *-(u)myen* 'when', *-(u)ni* and *-(u)nikka* 'when,
while', *-(n)untey* as a softened contrast, and *-tolok* with a negative as a possible
consequence, are not recorded, nor are the enders the Fragment lacks or the conjunctive
adverbials of main clauses.

## References

* [sohn-2009]
* [dixon-2009]
-/

@[expose] public section

namespace Sohn2009

open Korean Korean.Converb Clause

/-- A row of the summary table: an ender, a kind of linking it marks, and the part of the clause
it marks, `none` where the kind does not tell a focal from a supporting clause. -/
structure Row where
  converb : Converb
  linking : Linking
  role : Option Linking.Role
  deriving DecidableEq, Repr

/-- The rows of the summary table for the conjunctive suffixes of the Fragment. -/
def table : List Row :=
  [⟨go, .succession, some .supporting⟩, ⟨go, .unorderedAddition, none⟩,
    ⟨go, .sameEventAddition, some .supporting⟩, ⟨goseo, .succession, some .supporting⟩,
    ⟨myeonseo, .relativeTime, some .supporting⟩,
    ⟨myeonseo, .sameEventAddition, some .supporting⟩,
    ⟨eoseo, .succession, some .supporting⟩, ⟨eoseo, .relativeTime, some .supporting⟩,
    ⟨eoseo, .cause, some .supporting⟩, ⟨eoseo, .result, some .supporting⟩,
    ⟨eoseo, .realManner, some .supporting⟩, ⟨myeon, .conditional, some .supporting⟩,
    ⟨jiman, .contrast, some .supporting⟩, ⟨na, .contrast, some .supporting⟩,
    ⟨eodo, .conditional, some .supporting⟩, ⟨eodo, .contrast, some .supporting⟩,
    ⟨dorok, .relativeTime, some .supporting⟩, ⟨dorok, .purpose, some .focal⟩,
    ⟨nikka, .cause, some .supporting⟩, ⟨ni, .cause, some .supporting⟩,
    ⟨neunde, .elaboration, some .supporting⟩, ⟨ryeo, .purpose, some .focal⟩,
    ⟨reo, .purpose, some .focal⟩, ⟨daga, .succession, some .supporting⟩,
    ⟨jamaja, .relativeTime, some .supporting⟩, ⟨geona, .disjunction, none⟩,
    ⟨deunji, .disjunction, none⟩]

/-- The kinds of clause linking an ender marks. -/
def linkings (c : Converb) : Finset Linking :=
  ((table.filter (·.converb = c)).map (·.linking)).toFinset

/-- Every conjunctive suffix of the Fragment marks some kind of linking. -/
theorem linkings_nonempty (c : Converb) : (linkings c).Nonempty := by
  decide +revert

/-- A non-main clause is the focal clause of its linking exactly in purpose linking. -/
theorem role_eq_focal_iff : ∀ r ∈ table, (r.role = some .focal ↔ r.linking = .purpose) := by
  decide

/-- A non-main clause is the focal or the supporting clause of its linking except in unordered
addition and disjunction. -/
theorem role_isSome_iff : ∀ r ∈ table, (r.role.isSome ↔ r.linking.HasFocalClause) := by
  decide

/-- *-eoseo* marks temporal succession, cause, manner, result and relative time. -/
theorem linkings_eoseo :
    linkings eoseo = {.succession, .cause, .realManner, .result, .relativeTime} := by
  decide

end Sohn2009
