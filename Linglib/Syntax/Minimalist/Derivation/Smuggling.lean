/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Locality.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Reconstruction

/-!
# Smuggling

A constituent YP containing XP moves past W, which blocked XP: after the move YP c-commands W and
W no longer c-commands XP, so a probe above W that W would have intervened for now reaches XP.
On a derivation this is the step predicate `Derivation.IsSmugglingStep`, read
off the replayed stages through `Derivation.CCommandsAt`: the mover of the step contains `xp`,
`w` c-commands `xp` before the step, and after it the mover c-commands `w` and `w` no longer
c-commands `xp`. The blocking is rendered as `w`'s c-command of `xp`; the probe it matters for
is the consumer's to supply, as the passive study does when Infl finds the object closest once
PartP has carried it past the external argument in Spec-vP. Which heads let a constituent out
of their complement is a question each account answers for itself, and none is fixed here.
What a step smuggles is frozen, so a derivation that goes on to move it violates Freezing, which
smuggling accounts must therefore lift for the smuggling movement.

## Main results

* `Minimalist.Derivation.IsSmugglingStep.not_obeysFreezing_append_im`: moving the smuggled
  phrase on violates Freezing.

## References

* [collins-2005]
* [muller-1998]
-/

@[expose] public section

namespace Minimalist.Derivation

open SyntacticObject

variable {d : Derivation} {steps : List Step} {i : Nat} {xp w : SyntacticObject}

/-- Step `i` of `d` smuggles `xp` past `w` when its mover contains `xp`, which `w` c-commands
before the step, and after it the mover c-commands `w` and `w` no longer c-commands `xp`. -/
def IsSmugglingStep (d : Derivation) (i : Nat) (xp w : SyntacticObject) : Prop :=
  ∃ m ∈ d.mover? i,
    Contains m xp ∧ d.CCommandsAt i w xp ∧ d.CCommandsAt (i + 1) m w ∧
      ¬ d.CCommandsAt (i + 1) w xp

instance (d : Derivation) (i : Nat) (xp w : SyntacticObject) :
    Decidable (d.IsSmugglingStep i xp w) := by
  unfold IsSmugglingStep; infer_instance

theorem IsSmugglingStep.append (h : d.IsSmugglingStep i xp w) :
    (d.append steps).IsSmugglingStep i xp w := by
  obtain ⟨m, hm, hc, h₁, h₂, h₃⟩ := h
  have hi := lt_length_of_mem_mover? hm
  exact ⟨m, by rwa [mover?_append_of_lt hi], hc, (cCommandsAt_append_of_le hi.le).2 h₁,
    (cCommandsAt_append_of_le hi).2 h₂, fun h ↦ h₃ ((cCommandsAt_append_of_le hi).1 h)⟩

theorem IsSmugglingStep.frozen (h : d.IsSmugglingStep i xp w) : d.Frozen xp :=
  let ⟨m, hm, hc, _⟩ := h
  ⟨m, mem_movedItems_of_mem_mover? hm, hc⟩

theorem IsSmugglingStep.not_obeysFreezing_append_im (h : d.IsSmugglingStep i xp w)
    (side : Edge) : ¬ (d.append [.im xp side]).ObeysFreezing :=
  fun h' ↦ (obeysFreezing_append_im_iff.1 h').2 h.frozen

end Minimalist.Derivation
