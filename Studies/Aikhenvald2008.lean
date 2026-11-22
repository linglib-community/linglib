module

public import Mathlib.Algebra.Group.Idempotent
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

## Implementation notes

Each of the two examples has one medial clause with each completive, and its readings are those
of both clauses.

## References

* [aikhenvald-2008]
-/

public section

namespace Aikhenvald2008

open Manambu MedialMarker

/-- The inflection of a medial verb follows the switch-reference value of its marker. -/
theorem inflection_of_sr (m : MedialMarker) :
    (m.sr = some .ss → m.inflection = .uninflected) ∧
      (m.sr = some .ds → m.inflection = .partiallyInflected) ∧
      (m.sr = none → m.inflection = .uninflected ∨ m.inflection = .fullyInflected) := by
  decide +revert

/-- The only complex marker is *-ta:y* followed by *-kǝb*, with the switch-reference value of
*-ta:y* and a time begun before the next clause's and ending within it. -/
theorem complex_marker {m : MedialMarker} (h : 1 < m.morphs.length) :
    m.morphs = tay.morphs ++ keb.morphs ∧ m.sr = tay.sr := by
  decide +revert

theorem complex_marker_timing {T : Type*} [LinearOrder T] {i j : NonemptyInterval T} :
    Allen.relation i j ∈ taykeb.timing ↔ i.fst < j.fst ∧ j.fst < i.snd ∧ i.snd < j.snd := by
  simp only [timing, IntervalAlgebra.mem_inf, relation_mem_cotemporaneous, relation_mem_asSoonAs]
  exact ⟨fun ⟨⟨h₁, h₂⟩, _, _, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂⟩, h₁, h₂.le, h₃⟩⟩

theorem chainTiming_completive {ms : List MedialMarker} (hne : ms ≠ [])
    (h : ∀ m ∈ ms, m = ku ∨ m = k) : MedialForm.chainTiming ms = IntervalAlgebra.precedes := by
  have hm : ms.reverse.map MedialForm.timing =
      List.replicate ms.length IntervalAlgebra.precedes :=
    List.eq_replicate_iff.2 ⟨by simp, fun c hc ↦ by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
      rcases h m (List.mem_reverse.1 hm) with rfl | rfl <;> rfl⟩
  rw [MedialForm.chainTiming, hm, List.prod_replicate]
  exact IsIdempotentElem.pow_eq IntervalAlgebra.precedes_mul_precedes
    (List.length_pos_iff.2 hne).ne'

/-- In a chain of completive clauses, each ending before the next begins, the first event precedes
the final one. -/
theorem completive_chain {T : Type*} [LinearOrder T] {ms : List MedialMarker} (hne : ms ≠ [])
    (h : ∀ m ∈ ms, m = ku ∨ m = k) {t : NonemptyInterval T} {ts : List (NonemptyInterval T)}
    (hts : IntervalAlgebra.HoldsAlong (ms.reverse.map MedialForm.timing) t ts) :
    ((t :: ts).getLast (List.cons_ne_nil _ _)).Precedes t :=
  IntervalAlgebra.mem_toSetRel_precedes.1
    (chainTiming_completive hne h ▸ MedialForm.mem_toSetRel_chainTiming hts)

/-- *napa-* goes only with markers of succession or relative time. -/
theorem completive_temporal {m : MedialMarker} (h : m.WithCompletive) :
    m.completiveLinkings.Nonempty := by
  decide +revert

/-- A completive clause reads 'after' or 'because', and with *napa-* only 'after'. -/
theorem completive_readings {m : MedialMarker} (hm : m = ku ∨ m = k) :
    (Examples.ex18_17.readings.lookup "after" = some .acceptable ↔
        .relativeTime ∈ m.linkings) ∧
      (Examples.ex18_17.readings.lookup "because" = some .acceptable ↔ .cause ∈ m.linkings) ∧
      (Examples.ex18_53.readings.lookup "after" = some .acceptable ↔
        .relativeTime ∈ m.completiveLinkings) ∧
      (Examples.ex18_53.readings.lookup "because" = some .acceptable ↔
        .cause ∈ m.completiveLinkings) := by
  rcases hm with rfl | rfl <;> decide

end Aikhenvald2008
