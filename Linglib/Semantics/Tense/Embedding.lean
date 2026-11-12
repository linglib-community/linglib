module

public import Linglib.Semantics.Tense.Defs

/-!
# Embedded tense: the Upper Limit Constraint and past under past

A tense embedded under an attitude verb is evaluated from the attitude holder's now. Abusch makes
that local evaluation time an upper limit for the denotation of tenses, and accepts Heim's
construal of the constraint as a presupposition of every tense node: a tense's reference time
stands to its local evaluation time in a position of the nonfuture cell, `Tense.nonfuture`. That
cell contains the present and is closed under composition, so [no chain of tenses that each obey
the constraint reaches a later time](##Tense.compAlong_le_nonfuture): forward shifting needs an
operator such as *woll* that moves the evaluation time.

A past under a past attitude places its reference time before the attitude's now. In a language
with the Sequence of Tense rule the embedded past may instead be deleted and read as a zero tense
bound to the now, so it coincides with it. The positions `pastUnderPast` of an embedded past are
therefore the past cell, joined with the present cell where the rule applies. They [obey the
constraint](##Tense.pastUnderPast_le_nonfuture), [exhaust it exactly where the rule
applies](##Tense.pastUnderPast_eq_nonfuture_iff), and on either reading [leave the embedded time
before the utterance time](##Tense.comp_pastUnderPast_past).

## Implementation notes

Abusch motivates the constraint by the branching of the future across epistemic alternatives,
which `Studies/Abusch1997.lean` states on branching frames; the derivation of the cell from a
doxastic modal base is Klecha's (`Studies/Klecha2016.lean`).

## References

* [abusch-1997]
* [heim-1994-comments]
* [ogihara-1996]
-/

@[expose] public section

namespace Tense

open scoped Denotes
open scoped SetRel

/-- No chain of tenses that each obey the Upper Limit Constraint reaches a time after the one
above the chain. -/
theorem compAlong_le_nonfuture {cs : List (Finset Ordering)}
    (h : ∀ C ∈ cs, C ≤ nonfuture) : compAlong cs ≤ nonfuture := by
  induction cs with
  | nil => exact present_le_nonfuture
  | cons C cs ih =>
    rw [List.forall_mem_cons] at h
    exact (comp_le_comp (ih h.2) h.1).trans comp_nonfuture_nonfuture.le

/-- `pastUnderPast sot` is the cell of the positions an embedded past's reference time may take
against the attitude's now, where `sot` says whether the Sequence of Tense rule can delete it. A
genuine past precedes the now, and a deleted past is a zero tense bound to it. -/
def pastUnderPast (sot : Prop) [Decidable sot] : Finset Ordering :=
  ⟦past⟧ ⊔ if sot then ⟦present⟧ else ⊥

variable {sot : Prop} [Decidable sot]

theorem mem_pastUnderPast {o : Ordering} : o ∈ pastUnderPast sot ↔ o = .lt ∨ sot ∧ o = .eq := by
  by_cases h : sot <;> simp [pastUnderPast, h, Denotes.denote, denote]

/-- A time is a reading of a past under a past attitude exactly when it precedes the attitude's
now or, where the Sequence of Tense rule applies, is that now. -/
@[simp] theorem compare_mem_pastUnderPast {T : Type*} [LinearOrder T] (r p : T) :
    compare r p ∈ pastUnderPast sot ↔ r < p ∨ sot ∧ r = p := by
  rw [mem_pastUnderPast, compare_lt_iff_lt, compare_eq_iff_eq]

theorem lt_mem_pastUnderPast : .lt ∈ pastUnderPast sot :=
  mem_pastUnderPast.2 (.inl rfl)

/-- The simultaneous reading of a past under a past is available exactly where the Sequence of
Tense rule applies. -/
@[simp] theorem eq_mem_pastUnderPast_iff : .eq ∈ pastUnderPast sot ↔ sot := by
  simp [mem_pastUnderPast]

theorem pastUnderPast_pos (h : sot) : pastUnderPast sot = nonfuture := by
  simp [pastUnderPast, h, nonfuture_eq_past_sup_present]

theorem pastUnderPast_neg (h : ¬ sot) : pastUnderPast sot = ⟦past⟧ := by
  simp [pastUnderPast, h]

/-- Every reading of a past under a past obeys the Upper Limit Constraint. -/
theorem pastUnderPast_le_nonfuture : pastUnderPast sot ≤ nonfuture := by
  by_cases h : sot
  · exact (pastUnderPast_pos h).le
  · rw [pastUnderPast_neg h, nonfuture_eq_past_sup_present]
    exact le_sup_left

/-- The readings of a past under a past exhaust the Upper Limit Constraint exactly where the
Sequence of Tense rule applies. -/
theorem pastUnderPast_eq_nonfuture_iff :
    pastUnderPast sot = nonfuture ↔ sot :=
  ⟨fun h ↦ eq_mem_pastUnderPast_iff.1 (h ▸ (by decide : Ordering.eq ∈ nonfuture)),
    pastUnderPast_pos⟩

/-- On either reading a past under a past attitude leaves its reference time before the utterance
time, the simultaneous reading through the attitude's own past. -/
@[simp] theorem comp_pastUnderPast_past : comp (pastUnderPast sot) ⟦past⟧ = ⟦past⟧ := by
  by_cases h : sot
  · rw [pastUnderPast_pos h, nonfuture_eq_past_sup_present, comp_sup_left,
      comp_past_past, comp_present_left, sup_idem]
  · rw [pastUnderPast_neg h, comp_past_past]

end Tense
