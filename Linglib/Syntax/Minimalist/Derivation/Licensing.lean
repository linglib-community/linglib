/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Label.Head
public import Linglib.Syntax.Minimalist.Linearization.Replay

/-!
# Licensing a derivation

A licensing of Merge, a morphism of magmas from the syntactic objects into a magma with zero,
judges an object, `0` being the failure of Merge. A derivation is licensed when every stage is in
the licensing's domain, the object under construction and every copy extracted from it. A
licensing that judges only the derived object misses what its stages held: a moved item leaves a
trace, so whether it was merged before it was saturated shows only at the stages before it moved.
Stages are read off the replay, as `Derivation.CCommandsAt` reads c-command, so licensing decides,
and `LicensedAt.map_stageAt_ne_zero` returns the derivation's own stage. A licensing reads the
derivation with its own heads: a moved phrase leaves the trace of the item the licensing takes to
head it.

## Main definitions

* `Minimalist.Derivation.LicensedAt`: a stage of a derivation is in a licensing's domain.
* `Minimalist.Derivation.LicensedBy`: every stage is.

## Main statements

* `Minimalist.Derivation.LicensedAt.map_stageAt_ne_zero`: licensing at a stage is licensing of
  the derivation's own stage.
-/

@[expose] public section

namespace Minimalist.Derivation

variable {β : Type*} [Mul β] [Zero β] [Head β] (φ : SyntacticObject →ₙ* β) {d : Derivation}
  {n : ℕ}

/-- `φ` licenses stage `n` of `d`: the ordered configuration the replay reaches after `n` steps,
its movers leaving the traces of their heads under `φ`, is in its domain, the object and every
copy on the stack. -/
def LicensedAt (d : Derivation) (n : ℕ) : Prop :=
  ∃ c ∈ (d.take n).replay? (head ∘ φ), ∀ x ∈ c.current :: c.stack, φ x.toSyntacticObject ≠ 0

instance [DecidableEq β] (d : Derivation) (n : ℕ) : Decidable (d.LicensedAt φ n) := by
  unfold LicensedAt; infer_instance

/-- The stage licensing looks at is the derivation's own. -/
theorem LicensedAt.map_stageAt_ne_zero (h : d.LicensedAt φ n) :
    φ (d.stageAt n (head ∘ φ)) ≠ 0 := by
  obtain ⟨c, hc, hall⟩ := h
  rw [stageAt, final, ← (d.take n).replay?_faithful hc, Cfg.map_current]
  exact hall c.current List.mem_cons_self

/-- `φ` licenses `d` when it licenses every stage. -/
def LicensedBy (d : Derivation) : Prop := ∀ n ≤ d.length, d.LicensedAt φ n

instance [DecidableEq β] (d : Derivation) : Decidable (d.LicensedBy φ) := by
  unfold LicensedBy; infer_instance

end Minimalist.Derivation
