/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic

/-!
# Valid derivations

A step applies to a configuration when what it moves is there to move: an Internal Merge or an
extraction moves a term of the object, and `remerge` finds a copy on the stack. A derivation is
valid, `Derivation.IsValid`, when it starts from a leaf, each step applies to the configuration it
meets, and no token is merged twice. `Derivation.run` is total, so it carries an invalid derivation
on; validity is what a statement about stages assumes when it needs the steps to have applied.
[An initial segment of a valid derivation is valid](##Minimalist.Derivation.IsValid.take).

## References

* [collins-stabler-2016]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject
open Derivation (Cfg)

variable {τ : SyntacticObject → Option LexicalItem.Token}

/-- The step applies to the configuration: an Internal Merge or an extraction moves a term of the
object, and `remerge` finds a copy on the stack. -/
def Step.AppliesTo (c : Cfg SyntacticObject) : Step → Prop
  | .em _ _ => True
  | .im mover _ | .extract mover => mover ∈ c.current.terms
  | .remerge _ => c.stack ≠ []

/-- Each step of the list applies to the configuration the earlier ones reach. -/
def Step.ApplyFrom (τ : SyntacticObject → Option LexicalItem.Token) :
    List Step → Cfg SyntacticObject → Prop
  | [], _ => True
  | step :: steps, c => step.AppliesTo c ∧ Step.ApplyFrom τ steps (step.run c τ)

theorem Step.ApplyFrom.take :
    ∀ {steps : List Step} {c : Cfg SyntacticObject} (n : Nat),
      Step.ApplyFrom τ steps c → Step.ApplyFrom τ (steps.take n) c
  | _, _, 0, _ => by simp [Step.ApplyFrom]
  | [], _, _ + 1, _ => by simp [Step.ApplyFrom]
  | _ :: _, _, n + 1, ⟨h, hs⟩ => ⟨h, Step.ApplyFrom.take n hs⟩

namespace Derivation

/-- A derivation is valid when it starts from a lexical item or a trace, each step applies to the
configuration it meets, and no token is merged twice. -/
structure IsValid (d : Derivation) (τ : SyntacticObject → Option LexicalItem.Token := selHead) :
    Prop where
  /-- The initial object is a leaf. -/
  initial : d.initial.toLinearizedLeaf?.isSome
  /-- Each step applies to the configuration it meets. -/
  steps : Step.ApplyFrom τ d.steps ⟨d.initial, []⟩
  /-- No token is merged twice. -/
  nodup : d.lexTokens.Nodup

/-- An initial segment of a valid derivation is valid. -/
theorem IsValid.take {d : Derivation} (h : d.IsValid τ) (n : Nat) : (d.take n).IsValid τ :=
  ⟨h.initial, h.steps.take n, Multiset.nodup_of_le (d.lexTokens_take_le n) h.nodup⟩

end Derivation

end Minimalist
