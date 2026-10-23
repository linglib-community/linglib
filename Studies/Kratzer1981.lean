/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Semantics.Modality.Necessity

/-!
# Kratzer (1981): The Notional Category of Modality

This file formalizes the paper's practical-inference example, on the modal base and ordering
source semantics of `Modality.Necessity`. Someone wants two things, to become mayor
and to avoid the pub, while the circumstances are such that they become mayor only if they go
to the pub. The circumstances supply the modal base and the desires the ordering source, and
the two ideals pull apart, since a world where the speaker goes to the pub and becomes mayor and
one where they stay home and do not are incomparable, so the ordering is not connected. Of the
five conclusions the paper considers, the three necessities and impossibilities (that the
speaker should go to the pub, should avoid it, and could become mayor without it) fail, while
the two possibilities (that they could go and could avoid going) hold, under the paper's
limit-free necessity and its dual possibility.

The paper's section on conditionals treats an if-clause as restricting the modal base of the
modal in its matrix clause, the substrate's `Conditional.Restrictor.conditionalNecessity`,
and derives the kinds of conditional from the settings of the two backgrounds, material
implication from a totally realistic base and an empty ordering source
(`material_implication`), strict implication from an empty base and an empty ordering source
(`strict_implication`), counterfactuals from an empty base and a totally realistic ordering
source, the subject of the paper's companion on partition and revision, and deontic
conditionals from an empty base and an ordering source of what is morally good. The deontic
example is the argument against analyzing conditionals as modalized material implications.
Given that justice must be done, that analysis makes *if someone was treated unjustly, the
injustice must be amended for* and *... must be rewarded* both vacuously true
(`traditional_collapses`), while restricting an empty base by the antecedent and ordering by
what is morally good makes the first true and the second false
(`injustice_must_be_amended`, `not_injustice_must_be_rewarded`), a world where injustice is
amended for being closer to the good than one where it is rewarded, the truth conditions of
[lewis-1973].

## Implementation notes

The worlds are the four combinations of becoming mayor and going to the pub, so every claim
is decided once the modal base, the ordering source, and the operators are unfolded. The
example also fixes the reading of `bestWorlds`: the world that is at least as good as every
accessible world does not exist here, so the minimality reading, on which the best worlds are
the two ideal-realizing ones, is the one that agrees with the limit-free operators.

The deontic example's worlds are the situations with no injustice and those where an injustice
was amended for, rewarded, or neither; the ordering source of what is morally good is left
informal in the paper and is rendered by two ideals, that there is no injustice and that any
injustice is amended for. The section on conditionals is read from the revised version of the
paper in [kratzer-2012].

## References

* [kratzer-1981]
* [kratzer-2012] — Chapter 2, the revised version of the paper
* [lewis-1973]
-/

@[expose] public section


namespace Kratzer1981

open Modality

/-- A world records whether the speaker becomes mayor and whether they go to the pub regularly. -/
abbrev World := Bool × Bool

/-- The evaluation world, arbitrary since the backgrounds are constant. -/
def w₀ : World := (false, false)

/-- The relevant circumstances are that the speaker becomes mayor only by going to the pub. -/
def circumstances : Background World := Function.const World {fun w ↦ w.1 = true → w.2 = true}

/-- The speaker wants to become mayor and to avoid the pub. -/
def desires : Background World :=
  Function.const World {fun w ↦ w.1 = true, fun w ↦ w.2 = false}

/-- Decide a claim about the backgrounds and the ordering over the four worlds. -/
scoped macro "decide_worlds" : tactic =>
  `(tactic| (simp only [Background.mem_accessibleWorlds, Preorder.ofCriteria_le_iff,
      circumstances, desires, Function.const_apply, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, false_implies, implies_true, and_true]; decide))

theorem mayor_pub_incomparable :
    ¬ ((true, true) ≤[desires w₀] (false, false)) ∧
      ¬ ((false, false) ≤[desires w₀] (true, true)) := by
  decide_worlds

theorem pub_no_mayor_worst :
    ∀ v ∈ ({(true, true), (false, false)} : Set World),
      (v ≤[desires w₀] (false, true)) ∧
        ¬ ((false, true) ≤[desires w₀] v) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  decide_worlds

theorem no_dominant_world :
    ¬ ∃ w ∈ circumstances.accessibleWorlds w₀,
      ∀ v ∈ circumstances.accessibleWorlds w₀, (w ≤[desires w₀] v) := by
  decide_worlds

theorem mem_bestWorlds_iff (w : World) :
    w ∈ bestWorlds circumstances desires w₀ ↔ w = (true, true) ∨ w = (false, false) := by
  revert w
  simp only [mem_bestWorlds]
  decide_worlds

theorem limitAssumption : LimitAssumption circumstances desires w₀ :=
  .of_finite _ _ _

/-- Decide a verdict of the limit-free operators through the best worlds. -/
scoped macro "decide_verdict" : tactic =>
  `(tactic| (simp only [humanPossibility, humanNecessity_iff_necessity limitAssumption,
      necessity, ModalLogic.Box, mem_bestAccessible, mem_bestWorlds_iff, forall_eq_or_imp,
      forall_eq]; decide))

theorem not_must_pub : ¬ humanNecessity circumstances desires (·.2 = true) w₀ := by
  decide_verdict

theorem not_must_avoid : ¬ humanNecessity circumstances desires (·.2 = false) w₀ := by
  decide_verdict

theorem not_can_mayor_without_pub :
    ¬ humanPossibility circumstances desires (fun w ↦ w.1 = true ∧ w.2 = false) w₀ := by
  decide_verdict

theorem can_pub : humanPossibility circumstances desires (·.2 = true) w₀ := by
  decide_verdict

theorem can_avoid : humanPossibility circumstances desires (·.2 = false) w₀ := by
  decide_verdict

/-! ### Conditionals

An if-clause restricts the modal base of the modal in its matrix clause, so `(if α)
(necessarily β)` is the necessity of `β` at the base enlarged by `α`. The kinds of conditional
differ in the settings of the two backgrounds. -/

open Conditional.Restrictor

theorem material_implication {W : Type*} {f : Background W} (hf : f.IsTotallyRealistic)
    (α β : W → Prop) (w : W) :
    conditionalNecessity f ⊥ α β w ↔ (α w → β w) :=
  material_from_restrictor f α β w (hf w)

theorem strict_implication {W : Type*} (α β : W → Prop) (w : W) :
    conditionalNecessity ⊥ ⊥ α β w ↔ ∀ v, α v → β v := by
  rw [restrictor_eq_strict, Conditional.mem_strictImp_forall, Background.accessibleWorlds_bot]
  simp

theorem traditional_vacuous {W : Type*} (f : Background W) (α β : W → Prop) (w : W)
    (h : simpleNecessity f (fun v ↦ ¬ α v) w) : simpleNecessity f (fun v ↦ α v → β v) w :=
  fun v hv hα ↦ absurd hα (h v hv)

/-! #### The deontic example -/

/-- An injustice was amended for, rewarded, or neither. -/
inductive Redress where
  | amended
  | rewarded
  | neither
  deriving DecidableEq, Repr, Fintype

/-- A situation has no injustice, or an injustice and what became of it. -/
abbrev Situation := Option Redress

/-- Someone was treated unjustly. -/
def injustice (s : Situation) : Prop := s.isSome = true

/-- The injustice was amended for. -/
def amended (s : Situation) : Prop := s = some .amended

/-- The injustice was rewarded. -/
def rewarded (s : Situation) : Prop := s = some .rewarded

instance : DecidablePred injustice := fun s ↦ inferInstanceAs (Decidable (s.isSome = true))
instance : DecidablePred amended := fun s ↦ inferInstanceAs (Decidable (s = some .amended))
instance : DecidablePred rewarded := fun s ↦ inferInstanceAs (Decidable (s = some .rewarded))

/-- What is morally good is that there be no injustice and that any injustice be amended for. A
situation with amended injustice is not good, but it is closer to the good than one where the
injustice is rewarded or unredressed. -/
def morallyGood : Background Situation :=
  Function.const Situation {fun s ↦ ¬ injustice s, fun s ↦ injustice s → amended s}

/-- The morally accessible situations of the traditional analysis are those without injustice. -/
def morallyAccessible : Background Situation := Function.const Situation {fun s ↦ ¬ injustice s}

/-- Decide a claim about the backgrounds and the ordering over the four situations. -/
scoped macro "decide_situations" : tactic =>
  `(tactic| (simp only [Background.mem_accessibleWorlds,
      Background.mem_accessibleWorlds_restrict, Background.accessibleWorlds_bot,
      Set.mem_univ, true_and, Preorder.ofCriteria_le_iff, morallyGood, morallyAccessible,
      Function.const_apply, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp,
      forall_eq, false_implies, implies_true, and_true, injustice, amended, rewarded,
      Background.restrict, Pi.bot_apply, Set.bot_eq_empty, Set.mem_empty_iff_false,
      or_false]; decide))

theorem mem_bestWorlds_good_iff (s : Situation) :
    s ∈ bestWorlds ⊥ morallyGood none ↔ s = none := by
  revert s
  simp only [mem_bestWorlds]
  decide_situations

theorem mem_bestWorlds_injustice_iff (s : Situation) :
    s ∈ bestWorlds (Background.restrict ⊥ injustice) morallyGood none ↔
      s = some .amended := by
  revert s
  simp only [mem_bestWorlds]
  decide_situations

theorem limitAssumption_injustice :
    LimitAssumption (Background.restrict ⊥ injustice) morallyGood none :=
  .of_finite _ _ _

/-- Justice must be done (59), there being no injustice in the situations closest to the
good. -/
theorem justice_must_be_done :
    necessity ⊥ morallyGood (fun s ↦ ¬ injustice s) none := by
  simp only [necessity, ModalLogic.Box, mem_bestAccessible, mem_bestWorlds_good_iff, forall_eq]
  decide

/-- If someone was treated unjustly, the injustice must be amended for (60). -/
theorem injustice_must_be_amended :
    conditionalNecessity ⊥ morallyGood injustice amended none := by
  simp only [conditionalNecessity, necessity, ModalLogic.Box, mem_bestAccessible,
    mem_bestWorlds_injustice_iff, forall_eq]
  decide

/-- (61) is false, since the injustice need not be rewarded. -/
theorem not_injustice_must_be_rewarded :
    ¬ conditionalNecessity ⊥ morallyGood injustice rewarded none := by
  simp only [conditionalNecessity, necessity, ModalLogic.Box, mem_bestAccessible,
    mem_bestWorlds_injustice_iff, forall_eq]
  decide

/-- Under the traditional analysis (59) holds, and so (60) and (61) are both vacuously true. -/
theorem traditional_collapses :
    simpleNecessity morallyAccessible (fun s ↦ ¬ injustice s) none ∧
      simpleNecessity morallyAccessible (fun s ↦ injustice s → amended s) none ∧
        simpleNecessity morallyAccessible (fun s ↦ injustice s → rewarded s) none := by
  have h : simpleNecessity morallyAccessible (fun s ↦ ¬ injustice s) none := by
    simp only [simpleNecessity_iff]
    decide_situations
  exact ⟨h, traditional_vacuous _ _ _ _ h, traditional_vacuous _ _ _ _ h⟩

end Kratzer1981
