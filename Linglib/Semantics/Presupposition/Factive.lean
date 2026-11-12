module

public import Linglib.Semantics.Presupposition.Basic

/-!
# Factive predicates

A factive predicate, *know* or *regret that p*, presupposes its complement and asserts an attitude
toward it, so its sentence is the conditional event of the attitude on the complement. The
attitude is arbitrary: the doxastic box of *know* and the preference of *regret* are factive in the
same way. A predicate can instead entail its complement by asserting it beside the attitude. The
two analyses are [true at the same worlds](##Presupposition.posExt_factive) and part under
negation, where the factive is
[false only if the complement is true](##Presupposition.negExt_factive_eq_inter) and undefined
[where it is false](##Presupposition.gapExt_factive).

## Implementation notes

The complement is a bivalent proposition, so a presupposition of the complement itself does not
project through `factive`; `ConventionalImplicature.TwoDim.negFactive` treats a two-dimensional
complement under a negative factive. Karttunen's full and semi-factives differ in how the
presupposition projects from conditionals and questions, which one trivalent sentence does not
record, so the class stays on the lexical entry (`Presupposition.Factivity`).

## References

* [kiparsky-kiparsky-1970]
* [karttunen-1971b]
-/

@[expose] public section

namespace Presupposition

open Trivalent

variable {W : Type*} (att : (W → Prop) → W → Prop) (p : W → Prop) {w : W}

open Classical in
/-- The sentence of a factive predicate presupposes the complement `p` and asserts the attitude
`att` toward it. -/
noncomputable def factive : W → Trivalent := condEvent p (att p)

variable {att p}

@[simp] theorem factive_eq_true_iff : factive att p w = .true ↔ p w ∧ att p w := by
  simp [factive]

@[simp] theorem factive_eq_false_iff : factive att p w = .false ↔ p w ∧ ¬ att p w := by
  simp [factive]

@[simp] theorem factive_eq_undefined_iff : factive att p w = .undefined ↔ ¬ p w := by
  simp [factive]

variable (att p)

/-- A factive sentence is true where the complement holds beside the attitude, as the predicate
that asserts its complement is. -/
theorem posExt_factive : posExt (factive att p) = {w | att p w ∧ p w} := by
  ext w
  simp [and_comm]

/-- A factive sentence is false at the worlds where the predicate that asserts its complement is
false and the complement is true. -/
theorem negExt_factive_eq_inter :
    negExt (factive att p) = {w | ¬ (att p w ∧ p w)} ∩ {w | p w} := by
  ext w
  simp only [mem_negExt, factive_eq_false_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact ⟨fun h ↦ ⟨fun h' ↦ h.2 h'.1, h.1⟩, fun h ↦ ⟨h.2, fun ha ↦ h.1 ⟨ha, h.2⟩⟩⟩

/-- A factive sentence is undefined where the complement is false. -/
theorem gapExt_factive : gapExt (factive att p) = {w | ¬ p w} := by
  ext w
  simp

end Presupposition
