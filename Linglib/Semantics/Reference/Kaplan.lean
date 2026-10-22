/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Semantics.Reference.Character
public import Linglib.Semantics.Reference.Context.Tower
public import Mathlib.Algebra.Group.Action.End

/-!
# Kaplan's theory of indexicality

Kaplan's theory as Schlenker states it, over any type of contexts: an operator on characters that
evaluates its argument at another context is a *monster*, and Kaplan's thesis for English is that it
has none, its indexicals reading the speech-act context however deeply they are embedded, the
origin of the context tower.

## Main definitions

* `IsMonster`: an operator on characters that does not operate on contents.
* `shiftBy τ`: evaluation at the context `τ c v` computed from the context and the index, as the
  shifty operators of `Context/Overwrite.lean` do; `shift σ` is its index-independent case.
* `Kaplan.I`, `Kaplan.you`, `Kaplan.now`, `Kaplan.here`, `Kaplan.actually`: the pure indexicals,
  origin access patterns on the context tower.

## Main results

* `isMonster_shiftBy_iff`, `isMonster_shift_iff`: an operator evaluating at a computed or shifted
  context is a monster iff it moves some context.

## References

* [kaplan-1989]
* [schlenker-2011]
* [schlenker-2003]
* [anand-nevins-2004]
-/

@[expose] public section

namespace Kaplan

/-! ### Monsters -/

section Monster

variable {C V α β : Type*}

/-- An operator on characters is a monster when it does not operate on contents, so that what it
yields at a context is not determined by the content of its argument there ([kaplan-1989]). -/
def IsMonster (O : Character C V α → Character C V β) : Prop :=
  ¬ ∃ o : C → Content V α → Content V β, ∀ χ c, O χ c = o c (χ c)

/-- The operator that evaluates a character, at a context and an index, at the context `τ c v`
and the same index. -/
def shiftBy (τ : C → V → C) (χ : Character C V α) : Character C V α := fun c v ↦ χ (τ c v) v

@[simp] theorem shiftBy_apply (τ : C → V → C) (χ : Character C V α) (c : C) (v : V) :
    shiftBy τ χ c v = χ (τ c v) v := rfl

/-- Over values that can differ, an operator evaluating at a computed context is a monster iff the
computation moves some context at some index. -/
theorem isMonster_shiftBy_iff [Nontrivial α] (τ : C → V → C) :
    IsMonster (shiftBy τ : Character C V α → Character C V α) ↔ ∃ c v, τ c v ≠ c := by
  classical
  refine ⟨fun h ↦ ?_, fun ⟨c, v, hc⟩ ⟨o, ho⟩ ↦ ?_⟩
  · by_contra! hτ
    exact h ⟨fun _ f ↦ f, fun χ c ↦ funext fun v ↦ by simp [hτ]⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have h₁ := congrFun (ho (fun _ _ ↦ a) c) v
  have h₂ := congrFun (ho (Function.update (fun _ _ ↦ a) (τ c v) fun _ ↦ b) c) v
  simp only [shiftBy_apply, Function.update_self, Function.update_of_ne hc.symm] at h₁ h₂
  exact hab (h₁.trans h₂.symm)

/-- The operator that evaluates a character at the shifted context. -/
def shift (σ : Function.End C) : Character C V α → Character C V α := shiftBy fun c _ ↦ σ • c

@[simp] theorem shift_apply (σ : Function.End C) (χ : Character C V α) (c : C) :
    shift σ χ c = χ (σ • c) := rfl

/-- A shift moves some context iff it is not the identity. -/
theorem ne_one_iff_exists_smul_ne (σ : Function.End C) : σ ≠ 1 ↔ ∃ c : C, σ • c ≠ c :=
  show (σ : C → C) ≠ id ↔ _ from Function.ne_iff

/-- Over contents that can differ, a shift operator is a monster iff the shift moves some
context. -/
theorem isMonster_shift_iff [Nontrivial (Content V α)] (σ : Function.End C) :
    IsMonster (shift σ : Character C V α → Character C V α) ↔ σ ≠ 1 := by
  have := Function.nontrivial_of_nontrivial V α
  obtain ⟨f, g, h⟩ := exists_pair_ne (Content V α)
  have : Nonempty V := (Function.ne_iff.1 h).nonempty
  simp [shift, isMonster_shiftBy_iff, ne_one_iff_exists_smul_ne]

end Monster

/-! ### The English pure indexicals -/

open ContextTower

variable {W E P T : Type*}

/-- *I* is the agent of the speech-act context. -/
def I : AccessPattern (Context W E P T) E := .origin Context.agent

/-- *You* is the addressee of the speech-act context. -/
def you : AccessPattern (Context W E P T) E := .origin Context.addressee

/-- *Now* is the time of the speech-act context. -/
def now : AccessPattern (Context W E P T) T := .origin Context.time

/-- *Here* is the position of the speech-act context. -/
def here : AccessPattern (Context W E P T) P := .origin Context.position

/-- *Actually* is the world of the speech-act context. -/
def actually : AccessPattern (Context W E P T) W := .origin Context.world

end Kaplan
