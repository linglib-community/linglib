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
satisfaction specification: a relativized EPP ([hammerly-mathieu-2026]). A movement probe
[attracts](##Minimalist.Probe.Attracts) to its specifier a goal it agrees with, provided it
agrees with no other goal equally close. Merge is binary, so one step moves one goal
([coon-keine-2021]), and of several goals that would have to move in the same step
[none does](##Minimalist.Probe.not_attracts_of_ne), the Ban on Multiple Move. When every goal
the probe interacts with also satisfies it, as with a relativized EPP, the goals it agrees with
are all equally close and [it attracts the one goal it agrees
with](##Minimalist.Probe.attracts_iff_of_int_imp_sat). On a planar syntactic object the goal a
probe attracts is the mover of an Internal Merge step.

## Implementation notes

Movement is a search of its own, with its own conditions. The movement subfeatures of the
algorithm `Probe.Spec.agree` implements ([deal-2025a]), which move goals of the agreement search,
are not modelled.

## TODO

A probe that agrees with goals at several distances remerges them one after another, closest
first. `Probe.attract` reads out a goal only when it is the one goal attracted, and the sequence
of steps is not defined.

## References

* [hammerly-mathieu-2026]
* [coon-keine-2021]
* [deal-2025a]
-/

@[expose] public section

namespace Minimalist.Probe

variable {α β : Type*} [Preorder β] (p : Probe α) (s : Set α) (key : α → β)

/-- A movement probe attracts a goal it agrees with when it agrees with no other goal equally
close, neither of the two being closer than the other. Goals at different distances are met in
turn, and those equally close in one step. -/
def Attracts (a : α) : Prop :=
  p.AgreesWith s key a ∧
    ∀ ⦃b⦄, p.AgreesWith s key b → ¬ key a < key b → ¬ key b < key a → b = a

variable {p s key} {a b : α}

theorem Attracts.agreesWith (h : p.Attracts s key a) : p.AgreesWith s key a := h.1

/-- The Ban on Multiple Move of [hammerly-mathieu-2026]: a probe that agrees with two goals
equally close attracts neither. -/
theorem not_attracts_of_ne (hb : p.AgreesWith s key b) (hab : a ≠ b) (h : ¬ key a < key b)
    (h' : ¬ key b < key a) : ¬ p.Attracts s key a :=
  fun ha ↦ hab (ha.2 hb h h').symm

/-- When every goal a probe interacts with satisfies it, the goals it agrees with are all equally
close, and it attracts a goal exactly when that is the one goal it agrees with. -/
theorem attracts_iff_of_int_imp_sat (hp : ∀ a, p.int a → p.sat a) :
    p.Attracts s key a ↔ p.AgreesWith s key a ∧ ∀ b, p.AgreesWith s key b → b = a := by
  refine and_congr_right fun ha ↦ ⟨fun h b hb ↦ h hb ?_ ?_, fun h b hb _ _ ↦ h b hb⟩
  · exact hb.1.2 ha.1.1 (hp a ha.2)
  · exact ha.1.2 hb.1.1 (hp b hb.2)

variable (p s key) [Fintype α] [DecidableEq α] [DecidablePred (· ∈ s)]
  [DecidableRel ((· < ·) : β → β → Prop)]

instance : DecidablePred (p.Attracts s key) := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

instance : Decidable (∃! a, p.Attracts s key a) :=
  inferInstanceAs (Decidable (∃ a, p.Attracts s key a ∧ ∀ b, p.Attracts s key b → b = a))

/-- The goal a movement probe attracts, when it attracts exactly one. -/
def attract : Option α :=
  if h : ∃! a, p.Attracts s key a then some (Fintype.choose _ h) else none

variable {p s key}

theorem attract_eq_some_iff :
    p.attract s key = some a ↔ p.Attracts s key a ∧ ∀ b, p.Attracts s key b → b = a := by
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

end Minimalist.Probe

namespace Minimalist.PlanarSyntacticObject

variable {β : Type*} [Preorder β] [DecidableRel ((· < ·) : β → β → Prop)]

/-- The Internal Merge a movement probe searching the positions `s` of `t` triggers, those its head
c-commands or a part of them: the term at the goal it attracts re-merges. -/
def attractStep? (t : PlanarSyntacticObject) (p : Probe t.toRoseTree.Positions)
    (s : Set t.toRoseTree.Positions) [DecidablePred (· ∈ s)] (key : t.toRoseTree.Positions → β) :
        Option Step :=
  (p.attract s key).map fun q ↦ .im (t.termAt q)

theorem attractStep?_eq_some_iff {t : PlanarSyntacticObject} {p : Probe t.toRoseTree.Positions}
    {s : Set t.toRoseTree.Positions} [DecidablePred (· ∈ s)] {key : t.toRoseTree.Positions →
        β} {step : Step} :
    t.attractStep? p s key = some step ↔
      ∃ q, p.attract s key = some q ∧ step = .im (t.termAt q) := by
  simp [attractStep?, eq_comm]

end Minimalist.PlanarSyntacticObject
