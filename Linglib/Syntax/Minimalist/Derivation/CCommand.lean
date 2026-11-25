/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Replay

/-!
# C-command at a stage of a derivation

Movement reorders c-command, so what c-commands what depends on the stage. `Derivation.CCommandsAt`
is c-command in the object a derivation has built after a number of steps. It is [unchanged by
extending the derivation](##Minimalist.Derivation.cCommandsAt_append_of_le) and [invariant under an
injective relabelling that preserves
selection](##Minimalist.Derivation.cCommandsAt_map_iff).

## Implementation notes

* The predicate is decided on the replayed object when the replay succeeds, which is cheaper to
  evaluate than the unordered stage.
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

namespace Derivation

variable {ι : Type} [DecidableEq ι] [TraceLabel LexicalItem.Token ι]

/-- `x` c-commands `y` at stage `n` of `d`, under the trace encoder `τ`. -/
def CCommandsAt (d : Derivation ι) (n : Nat)
    (x y : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι :=
        TraceLabel.encoder) : Prop :=
  CCommands (d.stageAt n τ) x y

/-- Decided on the replayed object when the replay succeeds, which is cheaper to evaluate than the
stage itself. -/
instance (d : Derivation ι) (n : Nat)
    (x y : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι))
    (τ : SyntacticObject (SyntacticObject.Leaf LexicalItem.Token ι) → Option ι) : Decidable
        (d.CCommandsAt n x y τ) :=
  match h : (d.take n).externalize? τ with
  | some p => decidable_of_iff (CCommands p.toSyntacticObject x y) (by
      rw [CCommandsAt, ← d.externalize?_take_faithful n h])
  | none => inferInstanceAs (Decidable (CCommands (d.stageAt n τ) x y))

variable {d : Derivation} {steps : List Step} {n : Nat} {x y : SyntacticObject TokenLeaf}

theorem CCommandsAt.cCommands_stageAt (h : d.CCommandsAt n x y) :
    CCommands (d.stageAt n) x y := h

theorem cCommandsAt_append_of_le (h : n ≤ d.length) :
    (d.append steps).CCommandsAt n x y ↔ d.CCommandsAt n x y := by
  rw [CCommandsAt, CCommandsAt, stageAt_append_of_le h]

theorem cCommandsAt_map_iff {f : LexicalItem.Token → LexicalItem.Token} (hf : Function.Injective f)
    (hsel : LexicalItem.Token.PreservesSelection f) :
    (d.map f).CCommandsAt n (x.map f) (y.map f) ↔ d.CCommandsAt n x y := by
  rw [CCommandsAt, CCommandsAt,
    stageAt_map (τ := TraceLabel.encoder) (τ' := TraceLabel.encoder) d hf
      (fun s ↦ s.selectionHead_map hsel), cCommands_map_iff hf]

end Derivation

end Minimalist
