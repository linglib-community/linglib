module

public import Linglib.Data.Examples.Aikhenvald2008
public import Linglib.Fragments.Manambu.Clause

/-!
# Aikhenvald (2008): The Manambu Language of East Sepik, Papua New Guinea

This file checks the grammar's account of medial clauses (Chapter 18) against the Manambu
Fragment. Same-subject medial verbs are uninflected and different-subject ones partially
inflected, while a marker neutral to switch-reference takes an uninflected or a fully inflected
verb (§18.1). The markers are single suffixes except *-ta:y-kǝb*, *-ta:y* followed by *-kǝb*, whose
subject is the same because *-ta:y* is the same-subject marker (§18.6). The completive auxiliary
*napa-* is used only in temporal clauses (§18.1), and a clause with it has only temporal meaning
(§18.9): a completive clause reads 'after' or 'because' (18.17), and with *napa-* only 'after'
(18.53).

## Main statements

* `inflection_of_sr`: the inflection of a medial verb follows the switch-reference value of its
  marker.
* `complex_marker`: the only complex marker is *-ta:y* followed by *-kǝb*, with the
  switch-reference value of *-ta:y*.
* `completive_temporal`: every marker that *napa-* can carry encodes a temporal relation.
* `completive_readings`: a completive clause reads 'after' or 'because', and with *napa-* only
  'after'.

## Implementation notes

Each of the two examples has one medial clause with each completive, and its readings are those
of both clauses.

## Errata

Table 18.1 marks *-ta:y-kǝb*, with *-lǝk* and *-ga:y*, as not occurring with *napa-*, while the text
excludes only the last two (§18.1, §18.9). The Fragment follows the table.

## References

* [aikhenvald-2008]
-/

@[expose] public section

namespace Aikhenvald2008

open Manambu MedialMarker

theorem inflection_of_sr (m : MedialMarker) :
    (m.sr = some .ss → m.inflection = .uninflected) ∧
      (m.sr = some .ds → m.inflection = .partiallyInflected) ∧
      (m.sr = none → m.inflection = .uninflected ∨ m.inflection = .fullyInflected) := by
  decide +revert

theorem complex_marker {m : MedialMarker} (h : 1 < m.morphs.length) :
    m.morphs = tay.morphs ++ keb.morphs ∧ m.sr = tay.sr := by
  decide +revert

theorem completive_temporal {m : MedialMarker} (h : m.WithCompletive) :
    m.completiveRelations.Nonempty := by
  decide +revert

/-- A completive clause reads 'after' or 'because', and with *napa-* only 'after'. -/
theorem completive_readings {m : MedialMarker} (hm : m = ku ∨ m = k) :
    (Examples.ex18_17.readings.lookup "after" = some .acceptable ↔ .sequential ∈ m.relations) ∧
      (Examples.ex18_17.readings.lookup "because" = some .acceptable ↔ .causal ∈ m.relations) ∧
      (Examples.ex18_53.readings.lookup "after" = some .acceptable ↔
        .sequential ∈ m.completiveRelations) ∧
      (Examples.ex18_53.readings.lookup "because" = some .acceptable ↔
        .causal ∈ m.completiveRelations) := by
  rcases hm with rfl | rfl <;> decide

end Aikhenvald2008
