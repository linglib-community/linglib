/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Linglib.Core.Computability.Bimachine

/-!
# Elgot–Mezei composition and decomposition

A bimachine [run over the output of a subsequential transducer](##Bimachine.run_comp) is again a
bimachine, whose right automaton carries the map from states of the transducer to right states over
the image of the suffix. Conversely, [every bimachine is a right-to-left pass after a left-to-right
one](##Bimachine.run_eq_comp), the first marking each letter with its left state. So the
bimachine-computable functions are [closed under composition](##IsBimachineComputable.comp) and are
[the composites of the two scans](##isBimachineComputable_iff_exists_comp), and [those of
letter-to-letter machines](##isLetterToLetterBimachineComputable_iff_exists_comp) are the
composites of two Mealy passes.

## Implementation notes

The composition is direct, through the map-valued right state, where Mihov and Schulz's composition
of two bimachines goes through a subset construction; two bimachines compose here by decomposing
the first. Sakarovitch's decomposition has `Q × A` and `Q` in its intermediate alphabet and a first
pass with a final function; marking with `L × α` alone keeps the first pass a Mealy machine, and the
second pass then remembers whether it has read anything, for the final right block.

[UPSTREAM] candidate: `Mathlib.Computability.Bimachine`.

## References

* [elgot-mezei-1965]
* [eilenberg-1974]
* [reutenauer-schutzenberger-1991]
* [sakarovitch-2009]
* [mihov-schulz-2019]
-/

@[expose] public section

universe u v

variable {L R σ α β γ : Type*}

namespace Bimachine

/-! ### Composition with a left-to-right scan -/

section Comp

variable (B : Bimachine L R β γ) (T : SubsequentialTransducer σ α β)

/-- `B.comp T` runs `B` over the output of `T`. Its left state is the state of `T` and the left
state of `B` over the output so far; its right state maps the state of `T` entering the suffix to
the right state of `B` over the image of that suffix, `T`'s final output included. -/
@[simps]
def comp : Bimachine (σ × L) (σ → R) α γ where
  lInit := (T.start, B.lInit)
  lStep p a := (T.step p.1 a, B.lStateFrom p.2 (T.output p.1 a))
  rInit s := B.rState (T.finalOutput s)
  rStep m a s := B.rStateFrom (m (T.step s a)) (T.output s a)
  output p a m := B.emitted p.2 (T.output p.1 a) (m (T.step p.1 a))
  finalLeft m := B.finalLeft (m T.start)
  finalRight p := B.emitted p.2 (T.finalOutput p.1) B.rInit
    ++ B.finalRight (B.lStateFrom p.2 (T.finalOutput p.1))

@[simp] theorem lStateFrom_comp (p : σ × L) (xs : List α) :
    (B.comp T).lStateFrom p xs = (T.evalFrom p.1 xs, B.lStateFrom p.2 (T.emitted p.1 xs)) := by
  induction xs generalizing p <;> simp [lStateFrom_append, *]

@[simp] theorem rStateFrom_comp (m : σ → R) (xs : List α) (s : σ) :
    (B.comp T).rStateFrom m xs s = B.rStateFrom (m (T.evalFrom s xs)) (T.emitted s xs) := by
  induction xs generalizing s <;> simp [rStateFrom_append, *]

theorem emitted_comp (p : σ × L) (xs : List α) (m : σ → R) :
    (B.comp T).emitted p xs m = B.emitted p.2 (T.emitted p.1 xs) (m (T.evalFrom p.1 xs)) := by
  induction xs generalizing p <;> simp [emitted_append, *]

/-- The bimachine `B.comp T` computes the composite. -/
@[simp] theorem run_comp : (B.comp T).run = B.run ∘ T.run := by
  funext xs
  simp [run, lState, rState, emitted_comp, SubsequentialTransducer.run,
    SubsequentialTransducer.runFrom, emitted_append, rStateFrom_append, lStateFrom_append]

/-- A letter-to-letter machine run over a Mealy machine is letter-to-letter. -/
def LetterToLetter.comp {B : Bimachine L R β γ} (w : B.LetterToLetter) (T : Mealy σ α β) :
    (B.comp T.toSubsequentialTransducer).LetterToLetter where
  cell p a m := w.cell p.2 (T.output p.1 a) (m (T.step p.1 a))
  output_eq p a m := by simp [w.output_eq]
  finalLeft_eq _ := w.finalLeft_eq _
  finalRight_eq _ := by simp [w.finalRight_eq]

end Comp

/-! ### Decomposition into two passes -/

section Decomposition

variable (B : Bimachine L R α β)

/-- The left-to-right pass of a bimachine marks each letter with the left state before it. -/
@[simps]
def leftPass : Mealy L α (L × α) where
  start := B.lInit
  step := B.lStep
  output l a := (l, a)

@[simp] theorem evalFrom_leftPass (l : L) (xs : List α) :
    B.leftPass.evalFrom l xs = B.lStateFrom l xs := rfl

/-- The right-to-left pass of a bimachine, reading letters marked by `leftPass`, runs the right
automaton and emits each cell reversed. Its state is `none` until it reads a letter, when it emits
the final right block. -/
@[simps]
def rightPass : SubsequentialTransducer (Option R) (L × α) β where
  start := none
  step r p := some (B.rStep (r.getD B.rInit) p.2)
  output r p := (r.elim (B.finalRight (B.lStep p.1 p.2)) fun _ ↦ []).reverse
    ++ (B.output p.1 p.2 (r.getD B.rInit)).reverse
  finalOutput r := r.elim (B.finalLeft B.rInit ++ B.finalRight B.lInit).reverse
    fun r ↦ (B.finalLeft r).reverse

private theorem evalFrom_rightPass (l : L) (r : R) (xs : List α) :
    B.rightPass.evalFrom (some r) (B.leftPass.runFrom l xs).reverse
      = some (B.rStateFrom r xs) := by
  induction xs generalizing l <;> simp [Mealy.evalFrom_append, *]

private theorem emitted_rightPass (l : L) (r : R) (xs : List α) :
    B.rightPass.emitted (some r) (B.leftPass.runFrom l xs).reverse
      = (B.emitted l xs r).reverse := by
  induction xs generalizing l <;>
    simp [SubsequentialTransducer.emitted_append, evalFrom_rightPass, *]

/-- A bimachine is its right-to-left pass after its left-to-right pass ([sakarovitch-2009]
Prop. V.2.7). -/
theorem run_eq_comp : B.run = B.rightPass.runRight ∘ B.leftPass.run := by
  funext xs
  rcases List.eq_nil_or_concat xs with rfl | ⟨ys, a, rfl⟩
  · simp [run, SubsequentialTransducer.runRight, Mealy.run]
  · simp [run, lState, rState, SubsequentialTransducer.runRight, SubsequentialTransducer.run,
      SubsequentialTransducer.runFrom, Mealy.run, Mealy.runFrom_append, emitted_append,
      rStateFrom_append, lStateFrom_append, evalFrom_rightPass, emitted_rightPass, -rState_cons]

/-- The right-to-left pass of a letter-to-letter machine is a Mealy machine. -/
theorem LetterToLetter.isMealyComputable_rightPass {B : Bimachine L R α β} [Fintype R]
    (w : B.LetterToLetter) : IsMealyComputable B.rightPass.run := by
  refine B.rightPass.isMealyComputable_run (fun r p ↦ ?_) fun r ↦ ?_ <;>
    cases r <;> simp [w.output_eq, w.finalLeft_eq, w.finalRight_eq]

end Decomposition

end Bimachine

/-! ### The classes -/

section Classes

variable {f : List α → List β} {g : List β → List γ}

/-- A bimachine-computable function after a left-subsequential one is bimachine-computable. -/
theorem IsBimachineComputable.comp_isLeftSubsequential (hg : IsBimachineComputable g)
    (hf : IsLeftSubsequential f) : IsBimachineComputable (g ∘ f) := by
  classical
  obtain ⟨_, _, _, _, B, rfl⟩ := hg
  obtain ⟨_, _, T, rfl⟩ := hf
  exact ⟨_, inferInstance, _, inferInstance, B.comp T, B.run_comp T⟩

/-- A bimachine-computable function after a right-subsequential one is bimachine-computable. -/
theorem IsBimachineComputable.comp_isRightSubsequential (hg : IsBimachineComputable g)
    (hf : IsRightSubsequential f) : IsBimachineComputable (g ∘ f) := by
  rw [← isBimachineComputable_revConj_iff, List.revConj_comp]
  exact hg.revConj.comp_isLeftSubsequential hf

/-- The bimachine-computable functions are closed under composition, the functional case of the
composition theorem of Elgot and Mezei ([sakarovitch-2009] Th. IV.1.4). -/
theorem IsBimachineComputable.comp (hg : IsBimachineComputable g) (hf : IsBimachineComputable f) :
    IsBimachineComputable (g ∘ f) := by
  obtain ⟨_, _, _, _, B, rfl⟩ := hf
  rw [B.run_eq_comp, ← Function.comp_assoc]
  exact (hg.comp_isRightSubsequential B.rightPass.isRightSubsequential).comp_isLeftSubsequential
    B.leftPass.isLeftSubsequential

/-- A function is bimachine-computable exactly when it is a right-subsequential function after a
left-subsequential one, over some intermediate alphabet, Elgot and Mezei's decomposition
([sakarovitch-2009] Th. V.2.2, with Cor. V.2.5 for the converse). -/
theorem isBimachineComputable_iff_exists_comp {α : Type u} {β : Type v} {f : List α → List β} :
    IsBimachineComputable f ↔ ∃ (Z : Type u) (h : List α → List Z) (k : List Z → List β),
      IsLeftSubsequential h ∧ IsRightSubsequential k ∧ k ∘ h = f :=
  ⟨fun ⟨_, _, _, _, B, hB⟩ ↦ ⟨_, _, _, B.leftPass.isLeftSubsequential,
      B.rightPass.isRightSubsequential, hB ▸ B.run_eq_comp.symm⟩,
    fun ⟨_, _, _, hh, hk, e⟩ ↦ e ▸ hk.isBimachineComputable.comp hh.isBimachineComputable⟩

/-- A function of a letter-to-letter bimachine after a Mealy-computable one is the function of a
letter-to-letter bimachine. -/
theorem IsLetterToLetterBimachineComputable.comp_isMealyComputable
    (hg : IsLetterToLetterBimachineComputable g) (hf : IsMealyComputable f) :
    IsLetterToLetterBimachineComputable (g ∘ f) := by
  classical
  obtain ⟨_, _, _, _, B, ⟨w⟩, rfl⟩ := hg
  obtain ⟨_, _, T, rfl⟩ := hf
  refine ⟨_, inferInstance, _, inferInstance, B.comp T.toSubsequentialTransducer, ⟨w.comp T⟩, ?_⟩
  rw [B.run_comp, T.run_toSubsequentialTransducer]

/-- A function of a letter-to-letter bimachine after the mirror image of a Mealy-computable one is
the function of a letter-to-letter bimachine. -/
theorem IsLetterToLetterBimachineComputable.comp_of_isMealyComputable_revConj
    (hg : IsLetterToLetterBimachineComputable g) (hf : IsMealyComputable (List.revConj f)) :
    IsLetterToLetterBimachineComputable (g ∘ f) := by
  have h := (hg.revConj.comp_isMealyComputable hf).revConj
  rwa [← List.revConj_comp, List.revConj_revConj] at h

/-- A function is computed by a letter-to-letter bimachine exactly when it is a right-to-left Mealy
pass after a left-to-right one, over some intermediate alphabet. -/
theorem isLetterToLetterBimachineComputable_iff_exists_comp {α : Type u} {β : Type v}
    {f : List α → List β} :
    IsLetterToLetterBimachineComputable f ↔ ∃ (Z : Type u) (h : List α → List Z)
      (k : List Z → List β), IsMealyComputable h ∧ IsMealyComputable (List.revConj k) ∧ k ∘ h = f :=
  ⟨fun ⟨_, _, _, _, B, ⟨w⟩, hB⟩ ↦ ⟨_, _, _, B.leftPass.isMealyComputable,
      (List.revConj_revConj B.rightPass.run).symm ▸ w.isMealyComputable_rightPass,
      hB ▸ B.run_eq_comp.symm⟩,
    fun ⟨_, _, k, hh, hk, e⟩ ↦ e ▸
      (List.revConj_revConj k ▸
        (IsLetterToLetterBimachineComputable.of_mealyComputable hk).revConj :
        IsLetterToLetterBimachineComputable k).comp_isMealyComputable hh⟩

/-- The functions of letter-to-letter bimachines are closed under composition. -/
theorem IsLetterToLetterBimachineComputable.comp (hg : IsLetterToLetterBimachineComputable g)
    (hf : IsLetterToLetterBimachineComputable f) :
    IsLetterToLetterBimachineComputable (g ∘ f) := by
  obtain ⟨_, h, k, hh, hk, rfl⟩ := isLetterToLetterBimachineComputable_iff_exists_comp.mp hf
  rw [← Function.comp_assoc]
  exact (hg.comp_of_isMealyComputable_revConj hk).comp_isMealyComputable hh

end Classes
