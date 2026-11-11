/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Remnant

/-!
# Smuggling

A phrase that a blocker keeps out of reach can be carried past the blocker inside a larger one.
The smuggler YP *smuggles* the smugglee XP past the blocker W when YP contains XP, W blocks a
relation between XP and something higher, and YP moves to a position c-commanding W;
`Derivation.IsSmugglingStep` says this of a step of a derivation. In a derivation that merges no
token twice, [the blocker no longer c-commands the smugglee after the
step](##Minimalist.Derivation.IsSmugglingStep.not_cCommandsAt_succ). The step [freezes the
smugglee](##Minimalist.Derivation.IsSmugglingStep.frozen), so [a derivation that goes on to move it
violates Freezing](##Minimalist.Derivation.IsSmugglingStep.not_obeysFreezing), which smuggling
accounts must lift. Remnant movement is the converse, its mover having lost a phrase where the
smuggler carries one, and [no step is both for the same
phrase](##Minimalist.Derivation.IsSmugglingStep.not_isRemnantStep).

## Implementation notes

* Blocking is the blocker's c-command of the smugglee, which covers an intervener and not a
  barrier or a phase boundary. The relation blocked, and the probe that reaches the smugglee
  afterwards, are the consumer's to supply.

## References

* [collins-2005]
* [muller-1998]
-/

@[expose] public section

namespace Minimalist.Derivation

open SyntacticObject

variable {d : Derivation} {steps : List Step} {i j : Nat} {xp w : SyntacticObject}

/-- Step `i` of `d` smuggles `xp` past `w`: its mover contains `xp`, which `w` c-commands before
the step, and c-commands `w` after it. -/
def IsSmugglingStep (d : Derivation) (i : Nat) (xp w : SyntacticObject) : Prop :=
  ∃ m ∈ d.mover? i, Contains m xp ∧ d.CCommandsAt i w xp ∧ d.CCommandsAt (i + 1) m w

instance (d : Derivation) (i : Nat) (xp w : SyntacticObject) :
    Decidable (d.IsSmugglingStep i xp w) :=
  inferInstanceAs (Decidable (∃ m ∈ d.mover? i, _))

theorem IsSmugglingStep.lt_length (h : d.IsSmugglingStep i xp w) : i < d.length :=
  let ⟨_, hm, _⟩ := h
  lt_length_of_mem_mover? hm

theorem isSmugglingStep_append_of_lt (hi : i < d.length) :
    (d.append steps).IsSmugglingStep i xp w ↔ d.IsSmugglingStep i xp w := by
  rw [IsSmugglingStep, IsSmugglingStep, mover?_append_of_lt hi, cCommandsAt_append_of_le hi.le]
  simp only [cCommandsAt_append_of_le (Nat.succ_le_of_lt hi)]

theorem IsSmugglingStep.append (h : d.IsSmugglingStep i xp w) :
    (d.append steps).IsSmugglingStep i xp w :=
  (isSmugglingStep_append_of_lt h.lt_length).2 h

theorem isSmugglingStep_map_iff {f : LexicalItem.Token → LexicalItem.Token}
    (hf : Function.Injective f) (hsel : LexicalItem.Token.PreservesSelection f) :
    (d.map f).IsSmugglingStep i (xp.map f) (w.map f) ↔ d.IsSmugglingStep i xp w := by
  cases h : d.mover? i <;>
    simp [IsSmugglingStep, mover?_map, h, contains_map_iff hf, cCommandsAt_map_iff hf hsel]

/-- Smuggling works: in a derivation that merges no token twice, the blocker no longer c-commands
the smugglee after the step, neither being a bare trace. -/
theorem IsSmugglingStep.not_cCommandsAt_succ (h : d.IsSmugglingStep i xp w)
    (hd : d.lexTokens.Nodup) (hxp : xp.yield ≠ 0) (hw : w.yield ≠ 0) :
    ¬ d.CCommandsAt (i + 1) w xp := by
  obtain ⟨m, hm, hmx, hwx, hmw⟩ := h
  obtain ⟨step, hs, hsm⟩ := Option.bind_eq_some_iff.1 hm
  intro hc
  have hnd := run_take_succ hs ▸ hmw.nodup_yield_run_take hd
  have hsub := Step.terms_current_run_subset (τ := selHead) hsm (d.take i).run
  have hstage : d.stageAt (i + 1) = (step.run (d.take i).run).current :=
    congrArg Cfg.current (run_take_succ hs)
  exact not_cCommands_merge_replace
    (Multiset.nodup_add.1 <| Multiset.nodup_of_le (Step.yield_add_yield_le_yield_run hsm _) hnd).2.2
    hxp hw hmx hwx.cCommands_stageAt ((hstage ▸ hmw.cCommands_stageAt).mono hsub)
    ((hstage ▸ hc.cCommands_stageAt).mono hsub)

/-- A smuggling step freezes what it smuggles. -/
theorem IsSmugglingStep.frozen (h : d.IsSmugglingStep i xp w) : d.Frozen xp :=
  let ⟨m, hm, hc, _⟩ := h
  ⟨m, mem_movedItems_of_mem_mover? hm, hc⟩

/-- A derivation that smuggles a phrase and goes on to move it violates Freezing. -/
theorem IsSmugglingStep.not_obeysFreezing (h : d.IsSmugglingStep i xp w) (hij : i < j)
    (hj : xp ∈ d.mover? j) : ¬ d.ObeysFreezing :=
  let ⟨m, hm, hc, _⟩ := h
  fun hf ↦ obeysFreezing_iff_forall_mover?.1 hf hij m hm xp hj hc

/-- A step does not move a remnant of what the phrase it smuggles pronounces. -/
theorem IsSmugglingStep.not_isRemnantStep (h : d.IsSmugglingStep i xp w) {t : LexicalItem.Token}
    (ht : t ∈ xp.yield) : ¬ d.IsRemnantStep i t := by
  obtain ⟨m, hm, hc, -⟩ := h
  rintro ⟨m', hm', -, hn⟩
  obtain rfl := Option.mem_unique hm hm'
  exact hn (Multiset.mem_of_le (yield_le_of_mem_terms (mem_terms.2 hc.to_reflTransGen)) ht)

end Minimalist.Derivation
