/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic

/-!
# Relabelling a derivation

`Derivation.map f` renames the tokens of a derivation. Under an injective renaming that the trace
encoder commutes with, [a relabelled derivation reaches the relabelled
configuration](##Minimalist.Derivation.run_map), so [its stages are the relabelled
stages](##Minimalist.Derivation.stageAt_map) and what holds of a derivation of one shape holds of
every renaming of it.
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

variable {τ : SyntacticObject → Option LexicalItem.Token}

section Map

variable (f : LexicalItem.Token → LexicalItem.Token)

/-- The step with its tokens relabelled by `f`. -/
def Step.map : Step → Step
  | .em side item => .em side (item.map f)
  | .im mover side => .im (mover.map f) side
  | .extract mover => .extract (mover.map f)
  | .remerge side => .remerge side

@[simp] theorem Step.mover?_map (step : Step) :
    (step.map f).mover? = step.mover?.map (SyntacticObject.map f) := by
  cases step <;> rfl

namespace Derivation

/-- The derivation with its tokens relabelled by `f`. -/
def map (d : Derivation) : Derivation := ⟨d.initial.map f, d.steps.map (Step.map f)⟩

variable (d : Derivation)

@[simp] theorem length_map : (d.map f).length = d.length := List.length_map _

@[simp] theorem take_map (n : Nat) : (d.map f).take n = (d.take n).map f := by
  simp [map, take, List.map_take]

@[simp] theorem append_map (steps : List Step) :
    (d.append steps).map f = (d.map f).append (steps.map (Step.map f)) := by
  simp [map, append]

variable {f} {τ' : SyntacticObject → Option LexicalItem.Token}

theorem _root_.Minimalist.Step.run_map (hf : Function.Injective f)
    (hτ : ∀ s, τ' (s.map f) = (τ s).map f) (step : Step) (c : Cfg SyntacticObject) :
    (step.map f).run (c.map (SyntacticObject.map f)) τ' =
      (step.run c τ).map (SyntacticObject.map f) := by
  rcases c with ⟨cur, _ | ⟨m, st⟩⟩ <;> cases step <;>
    simp [Step.map, Step.run, Step.apply, Cfg.map, deleteAccessible, replace_map hf,
      headTrace_map hτ]

/-- A relabelled derivation reaches the relabelled configuration, under an injective relabelling
the trace encoder commutes with. -/
theorem run_map (hf : Function.Injective f) (hτ : ∀ s, τ' (s.map f) = (τ s).map f) :
    (d.map f).run τ' = (d.run τ).map (SyntacticObject.map f) := by
  have key : ∀ (steps : List Step) (c : Cfg SyntacticObject),
      (steps.map (Step.map f)).foldl (fun c step ↦ step.run c τ')
          (c.map (SyntacticObject.map f)) =
        (steps.foldl (fun c step ↦ step.run c τ) c).map (SyntacticObject.map f) := by
    intro steps
    induction steps with
    | nil => intro c; rfl
    | cons step steps ih =>
      intro c
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, Step.run_map hf hτ, ih]
  exact key d.steps ⟨d.initial, []⟩

theorem stageAt_map (hf : Function.Injective f) (hτ : ∀ s, τ' (s.map f) = (τ s).map f)
    (n : Nat) : (d.map f).stageAt n τ' = (d.stageAt n τ).map f := by
  rw [stageAt, stageAt, take_map, final, final, run_map (d.take n) hf hτ, Cfg.map_current]

variable (f)

theorem movedItems_map : (d.map f).movedItems = d.movedItems.map (SyntacticObject.map f) := by
  simp [movedItems, map, List.filterMap_map, List.map_filterMap]

theorem mover?_map (i : ℕ) : (d.map f).mover? i = (d.mover? i).map (SyntacticObject.map f) := by
  rw [mover?, mover?, map]
  simp only [List.getElem?_map]
  cases d.steps[i]? <;> simp

end Derivation

end Map

end Minimalist
