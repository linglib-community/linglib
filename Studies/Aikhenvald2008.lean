module

public import Mathlib.Algebra.Group.Idempotent
public import Linglib.Languages.Manambu.Clause
public import Linglib.Logic.Temporal.IntervalAlgebra

/-!
# Aikhenvald (2008): The Manambu Language of East Sepik, Papua New Guinea

This file checks the grammar's account of medial clauses (Chapter 18) against the Manambu
Fragment. Same-subject medial verbs are uninflected and different-subject ones partially
inflected, while a marker neutral to switch-reference takes an uninflected or a fully inflected
verb (§18.1). A marker places the time of its clause relative to the next clause's (§18.1), and
`timing` gives each marker the cell of Allen relations it allows: the completives before the next
clause's time, *-ta:y* begun before it and overlapping it, *-taka* ending as it begins, and
*-kǝb* begun before it and ending as it begins or within it. The only complex marker,
*-ta:y-kǝb*, has the same subject because *-ta:y* is the same-subject marker, and its time begins
before the next clause's and overlaps it (§18.6). A chain of completive clauses presents its
events one after another (§18.10).

## Implementation notes

*-ta:y-kǝb* takes the meet of its parts' cells, and the causal *-lǝk* and the conditional *-ga:y*
leave the time open. The readings of the grammar's examples of completive clauses, with and
without the completive auxiliary *napa-* (18.17, 18.53), are checked in
`Studies/Aikhenvald2009.lean`, against the kinds of clause linking the later chapter gives the
markers.

## References

* [aikhenvald-2008]
-/

@[expose] public section

namespace Aikhenvald2008

open Manambu MedialMarker

/-- The inflection of a medial verb follows the switch-reference value of its marker. -/
theorem inflection_of_sr (m : MedialMarker) :
    (m.switchReference = some .ss → m.inflection = .uninflected) ∧
      (m.switchReference = some .ds → m.inflection = .partiallyInflected) ∧
      (m.switchReference = none →
        m.inflection = .uninflected ∨ m.inflection = .fullyInflected) := by
  decide +revert

/-! ### The times of medial clauses -/

/-- The cell of a time begun before the next clause's and overlapping it. -/
@[irreducible]
def cotemporaneous : IntervalAlgebra :=
  IntervalAlgebra.ofPred fun r ↦ r.fstFst = .lt ∧ r.sndFst = .gt

/-- The cell of a time ending where the next clause's begins. -/
@[irreducible]
def immediateSequence : IntervalAlgebra := IntervalAlgebra.ofPred (·.sndFst = .eq)

/-- The cell of a time begun before the next clause's and ending as it begins or within it. -/
@[irreducible]
def asSoonAs : IntervalAlgebra :=
  IntervalAlgebra.ofPred fun r ↦ r.fstFst = .lt ∧ r.sndFst ≠ .lt ∧ r.sndSnd = .lt

section

variable {T : Type*} [LinearOrder T] {i j : NonemptyInterval T}

@[simp] theorem relation_mem_cotemporaneous :
    Allen.relation i j ∈ cotemporaneous ↔ i.fst < j.fst ∧ j.fst < i.snd := by
  rw [cotemporaneous, IntervalAlgebra.mem_ofPred]
  simp [Allen.relation, Allen.ofEndpoints, compare_lt_iff_lt, compare_gt_iff_gt]

@[simp] theorem relation_mem_immediateSequence :
    Allen.relation i j ∈ immediateSequence ↔ i.snd = j.fst := by
  rw [immediateSequence, IntervalAlgebra.mem_ofPred]
  simp [Allen.relation, Allen.ofEndpoints]

@[simp] theorem relation_mem_asSoonAs :
    Allen.relation i j ∈ asSoonAs ↔ i.fst < j.fst ∧ j.fst ≤ i.snd ∧ i.snd < j.snd := by
  rw [asSoonAs, IntervalAlgebra.mem_ofPred]
  simp [Allen.relation, Allen.ofEndpoints, compare_lt_iff_lt]

end

/-- The cell in which a marker places the time of its clause relative to the next clause's. -/
def timing : MedialMarker → IntervalAlgebra
  | ku | k => IntervalAlgebra.precedes
  | tay => cotemporaneous
  | taka => immediateSequence
  | keb => asSoonAs
  | taykeb => cotemporaneous ⊓ asSoonAs
  | n => IntervalAlgebra.ofPosition {.lt, .eq}
  | lek | gay => ⊤

/-- The only complex marker is *-ta:y* followed by *-kǝb*, with the switch-reference value of
*-ta:y*. -/
theorem complex_marker {m : MedialMarker} (h : 1 < m.morphs.length) :
    m.morphs = tay.morphs ++ keb.morphs ∧ m.switchReference = tay.switchReference := by
  decide +revert

theorem complex_marker_timing {T : Type*} [LinearOrder T] {i j : NonemptyInterval T} :
    Allen.relation i j ∈ timing taykeb ↔ i.fst < j.fst ∧ j.fst < i.snd ∧ i.snd < j.snd := by
  simp only [timing, IntervalAlgebra.mem_inf, relation_mem_cotemporaneous, relation_mem_asSoonAs]
  exact ⟨fun ⟨⟨h₁, h₂⟩, _, _, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₂⟩, h₁, h₂.le, h₃⟩⟩

theorem prod_timing_completive {ms : List MedialMarker} (hne : ms ≠ [])
    (h : ∀ m ∈ ms, m = ku ∨ m = k) : (ms.map timing).prod = IntervalAlgebra.precedes := by
  have hm : ms.map timing = List.replicate ms.length IntervalAlgebra.precedes :=
    List.eq_replicate_iff.2 ⟨by simp, fun c hc ↦ by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hc
      rcases h m hm with rfl | rfl <;> rfl⟩
  rw [hm, List.prod_replicate]
  exact IsIdempotentElem.pow_eq IntervalAlgebra.precedes_mul_precedes
    (List.length_pos_iff.2 hne).ne'

/-- In a chain of completive clauses, each ending before the next begins, the first event precedes
the final one: `ts` are the times of the medial clauses from the last back to the first, and `t`
the time of the final clause. -/
theorem completive_chain {T : Type*} [LinearOrder T] {ms : List MedialMarker} (hne : ms ≠ [])
    (h : ∀ m ∈ ms, m = ku ∨ m = k) {t : NonemptyInterval T} {ts : List (NonemptyInterval T)}
    (hts : IntervalAlgebra.HoldsAlong (ms.reverse.map timing) t ts) :
    ((t :: ts).getLast (List.cons_ne_nil _ _)).Precedes t :=
  IntervalAlgebra.mem_toSetRel_precedes.1 <|
    prod_timing_completive (ms := ms.reverse) (by simpa using hne) (by simpa using h) ▸
      hts.mem_toSetRel_prod

end Aikhenvald2008
