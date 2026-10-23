/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Probe.Minimal
public import Linglib.Syntax.Minimalist.SyntacticObject.Position
public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Mathlib.Data.Fintype.Inv

/-!
# Movement probes

A head may carry conditions on movement as well as on agreement, each an interaction and a
satisfaction specification, a relativized EPP. A movement probe attracts the goal it agrees with to
its specifier, and since Merge is binary it attracts at most one: a probe that agrees with two goals
attracts neither, the Ban on Multiple Move. On a linearized syntactic object a probe on a head
searches the positions the head c-commands, and the goal it attracts is the mover of an Internal
Merge step.

## Main definitions

* `Minimalist.Probe.attract`: the goal a movement probe attracts.
* `Minimalist.LinearizedSyntacticObject.attractStep?`: the Internal Merge a probe on a head
  triggers. Its domain is the positions the head c-commands, or a part of them such as the nominals.

## Main results

* `Minimalist.Probe.attract_eq_some_iff`: a probe attracts the one goal it agrees with.
* `Minimalist.Probe.attract_eq_none_of_ne`: the Ban on Multiple Move.
* `Minimalist.LinearizedSyntacticObject.attractStep?_eq_some_iff`: the mover of the step is the term
  at the attracted position.

## Implementation notes

Movement is a search of its own, with its own conditions. The movement subfeatures of the
algorithm `Probe.Spec.agree` implements, which move goals of the agreement search, are not
modelled.

## References

* [hammerly-mathieu-2026]
* [coon-keine-2021]
* [deal-2025a]
-/

@[expose] public section

namespace Minimalist.Probe

variable {α β : Type*} [Preorder β] [Fintype α] [DecidableEq α] (p : Probe α) (s : Set α)
  [DecidablePred (· ∈ s)] (key : α → β) [DecidableRel ((· < ·) : β → β → Prop)]

instance : Decidable (∃! a, p.AgreesWith s key a) :=
  inferInstanceAs (Decidable (∃ a, p.AgreesWith s key a ∧ ∀ b, p.AgreesWith s key b → b = a))

/-- The goal a movement probe attracts, the one goal it agrees with. Binary Merge cannot move two
goals at once ([coon-keine-2021]), and a probe that agrees with several attracts none, the Ban on
Multiple Move of [hammerly-mathieu-2026]. -/
def attract : Option α :=
  if h : ∃! a, p.AgreesWith s key a then some (Fintype.choose _ h) else none

variable {p s key} {a b : α}

theorem attract_eq_some_iff :
    p.attract s key = some a ↔ p.AgreesWith s key a ∧ ∀ b, p.AgreesWith s key b → b = a := by
  unfold attract
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨Fintype.choose_spec _ h, fun b hb ↦ h.unique hb (Fintype.choose_spec _ h)⟩
    · rintro ⟨ha, hu⟩
      exact hu _ (Fintype.choose_spec _ h)
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    rintro ⟨ha, hu⟩
    exact h ⟨a, ha, hu⟩

theorem attract_eq_none_of_ne (ha : p.AgreesWith s key a) (hb : p.AgreesWith s key b)
    (hab : a ≠ b) : p.attract s key = none :=
  Option.eq_none_iff_forall_ne_some.2 fun c hc ↦ by
    obtain ⟨-, hu⟩ := attract_eq_some_iff.1 hc
    exact hab ((hu a ha).trans (hu b hb).symm)

end Minimalist.Probe

namespace Minimalist.LinearizedSyntacticObject

variable {β : Type*} [Preorder β] [DecidableRel ((· < ·) : β → β → Prop)]

/-- The Internal Merge a movement probe searching the positions `s` of `t` triggers, those its head
c-commands or a part of them: the term at the goal it attracts re-merges. -/
def attractStep? (t : LinearizedSyntacticObject) (p : Probe t.val.Positions)
    (s : Set t.val.Positions) [DecidablePred (· ∈ s)] (key : t.val.Positions → β) : Option Step :=
  (p.attract s key).map fun q ↦ .im (t.termAt q)

theorem attractStep?_eq_some_iff {t : LinearizedSyntacticObject} {p : Probe t.val.Positions}
    {s : Set t.val.Positions} [DecidablePred (· ∈ s)] {key : t.val.Positions → β} {step : Step} :
    t.attractStep? p s key = some step ↔
      ∃ q, p.attract s key = some q ∧ step = .im (t.termAt q) := by
  simp [attractStep?, eq_comm]

end Minimalist.LinearizedSyntacticObject
