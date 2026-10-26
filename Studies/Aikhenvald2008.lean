module

public import Linglib.Data.Examples.Aikhenvald2008
public import Linglib.Fragments.Manambu.Clause

/-!
# Aikhenvald (2008): The Manambu Language of East Sepik, Papua New Guinea

This file checks the grammar's account of medial clauses (Chapter 18) against the Manambu
Fragment. Same-subject medial verbs are uninflected and different-subject ones partially
inflected, while a marker neutral to switch-reference takes an uninflected or a fully inflected
verb (§18.1). The only complex marker, *-ta:y-kǝb*, has the same subject because *-ta:y* is the
same-subject marker, and its time begins before the next clause's and overlaps it (§18.6). A chain
of completive clauses presents its events one after another (§18.10). The completive auxiliary
*napa-* is used only in temporal clauses (§18.1), and a clause with it has only temporal meaning
(§18.9): a completive clause reads 'after' or 'because' (18.17), with *napa-* only 'after' (18.53).

## Main statements

* `inflection_of_sr`: the inflection of a medial verb follows the switch-reference value of its
  marker.
* `complex_marker`, `complex_marker_timing`: the only complex marker is *-ta:y* followed by
  *-kǝb*, with the switch-reference value of *-ta:y* and a time begun before the next clause's
  and ending within it.
* `completive_chain`: in a chain of completive clauses the first event precedes the final one.
* `completive_temporal`, `completive_readings`: *napa-* goes only with markers that encode a
  temporal relation, and leaves a completive clause reading 'after' but not 'because'.

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

theorem complex_marker_timing {T : Type*} [LinearOrder T] {i j : NonemptyInterval T} :
    Allen.relation i j ∈ taykeb.timing ↔ i.fst < j.fst ∧ j.fst < i.snd ∧ i.snd < j.snd := by
  simp only [timing, Finset.mem_inter, relation_mem_cotemporaneous, relation_mem_asSoonAs]
  exact ⟨fun ⟨⟨h₁, h₂⟩, _, _, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂⟩, h₁, h₂.le, h₃⟩⟩

/-- In a chain of completive clauses the first event precedes the final one. -/
theorem completive_chain {ms : List MedialMarker} (hne : ms ≠ []) (h : ∀ m ∈ ms, m = ku ∨ m = k) :
    MedialForm.chainTiming ms = Allen.precedes := by
  induction ms using List.reverseRecOn with
  | nil => exact absurd rfl hne
  | append_singleton ms m ih =>
    have hm : MedialForm.timing m = Allen.precedes := by
      rcases h m (by simp) with rfl | rfl <;> rfl
    rw [MedialForm.chainTiming_concat, hm]
    rcases eq_or_ne ms [] with rfl | hms
    · rw [MedialForm.chainTiming_nil]
      decide +kernel
    · rw [ih hms fun m' hm' ↦ h m' (by simp [hm']), Allen.comp_precedes_precedes]

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
