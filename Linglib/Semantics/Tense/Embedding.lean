module

public import Linglib.Semantics.Tense.Defs

/-!
# Embedded tense: the Upper Limit Constraint and past under past

A tense embedded under an attitude verb is evaluated from the attitude holder's now. Abusch makes
that local evaluation time an upper limit for the denotation of tenses, and accepts Heim's
construal of the constraint as a presupposition of every tense node. As a constraint on how the
reference time of a tense stands to its local evaluation time, the Upper Limit Constraint is the
cell of the past and the present positions (`upperLimitConstraint`).

A past under a past attitude places its reference time before the attitude's now. In a language
with the Sequence of Tense rule the embedded past may instead be deleted and read as a zero tense
bound to the now, so it coincides with it. The positions an embedded past may take are therefore
the past cell, joined with the present cell where the rule applies (`pastUnderPast`). Every such
position obeys the Upper Limit Constraint, and the positions exhaust it exactly where the rule
applies.

## Main definitions

* `Tense.upperLimitConstraint`: the Upper Limit Constraint, the cell of the past and the present.
* `Tense.pastUnderPast`: the positions of an embedded past against the attitude's now.

## Main results

* `Tense.pastUnderPast_le_upperLimitConstraint`, `Tense.pastUnderPast_eq_upperLimitConstraint_iff`:
  every reading of a past under a past obeys the constraint, and the readings exhaust it exactly
  where the Sequence of Tense rule applies.
* `Tense.eq_mem_pastUnderPast_iff`: the simultaneous reading is available exactly where the rule
  applies.

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

/-- The Upper Limit Constraint is the cell of the positions a tense's reference time may take
against its local evaluation time, before it or at it and never after it. -/
def upperLimitConstraint : Finset Ordering := ⟦future⟧ᶜ

theorem upperLimitConstraint_eq_past_sup_present : upperLimitConstraint = ⟦past⟧ ⊔ ⟦present⟧ :=
  past_sup_present.symm

theorem mem_upperLimitConstraint {o : Ordering} : o ∈ upperLimitConstraint ↔ o ≠ .gt := by
  simp [upperLimitConstraint, Denotes.denote, denote]

@[simp] theorem compare_mem_upperLimitConstraint {T : Type*} [LinearOrder T] (r p : T) :
    compare r p ∈ upperLimitConstraint ↔ r ≤ p :=
  compare_mem_compl_future r p

@[simp] theorem mem_toSetRel_upperLimitConstraint {T : Type*} [PartialOrder T] {p r : T} :
    p ~[toSetRel upperLimitConstraint] r ↔ r ≤ p := by
  rw [upperLimitConstraint_eq_past_sup_present, toSetRel_sup, Set.mem_union, mem_toSetRel_past,
    mem_toSetRel_present, le_iff_lt_or_eq]

/-- `pastUnderPast sot` is the cell of the positions an embedded past's reference time may take
against the attitude's now, where `sot` says whether the Sequence of Tense rule can delete it. A
genuine past precedes the now, and a deleted past is a zero tense bound to it. -/
def pastUnderPast (sot : Prop) [Decidable sot] : Finset Ordering :=
  ⟦past⟧ ⊔ if sot then ⟦present⟧ else ⊥

variable {sot : Prop} [Decidable sot]

theorem mem_pastUnderPast {o : Ordering} : o ∈ pastUnderPast sot ↔ o = .lt ∨ sot ∧ o = .eq := by
  by_cases h : sot <;> simp [pastUnderPast, h, Denotes.denote, denote]

theorem lt_mem_pastUnderPast : .lt ∈ pastUnderPast sot :=
  mem_pastUnderPast.2 (.inl rfl)

/-- The simultaneous reading of a past under a past is available exactly where the Sequence of
Tense rule applies. -/
@[simp] theorem eq_mem_pastUnderPast_iff : .eq ∈ pastUnderPast sot ↔ sot := by
  simp [mem_pastUnderPast]

theorem pastUnderPast_pos (h : sot) : pastUnderPast sot = upperLimitConstraint := by
  simp [pastUnderPast, h, upperLimitConstraint_eq_past_sup_present]

theorem pastUnderPast_neg (h : ¬ sot) : pastUnderPast sot = ⟦past⟧ := by
  simp [pastUnderPast, h]

/-- Every reading of a past under a past obeys the Upper Limit Constraint. -/
theorem pastUnderPast_le_upperLimitConstraint : pastUnderPast sot ≤ upperLimitConstraint := by
  by_cases h : sot
  · exact (pastUnderPast_pos h).le
  · rw [pastUnderPast_neg h, upperLimitConstraint_eq_past_sup_present]
    exact le_sup_left

/-- The readings of a past under a past exhaust the Upper Limit Constraint exactly where the
Sequence of Tense rule applies. -/
theorem pastUnderPast_eq_upperLimitConstraint_iff :
    pastUnderPast sot = upperLimitConstraint ↔ sot :=
  ⟨fun h ↦ eq_mem_pastUnderPast_iff.1 (h ▸ mem_upperLimitConstraint.2 (by decide)),
    pastUnderPast_pos⟩

end Tense
