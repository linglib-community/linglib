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
relation between XP and something higher, and YP moves to a position c-commanding W. This is a
property of one movement, `SyntacticObject.Smuggles`, and [the blocker no longer c-commands the
smugglee after it](##Minimalist.SyntacticObject.Smuggles.not_cCommands) when the smuggler and the
remainder share no token, as in [a valid
derivation](##Minimalist.Derivation.IsSmugglingStep.not_cCommandsAt_succ).
`Derivation.IsSmugglingStep` says of a step that [it is such a
movement](##Minimalist.Derivation.IsSmugglingStep.smuggles). The step [freezes the
smugglee](##Minimalist.Derivation.IsSmugglingStep.frozen), so [a derivation that goes on to move it
violates Freezing](##Minimalist.Derivation.IsSmugglingStep.not_obeysFreezing), which smuggling
accounts must lift. Remnant movement is the converse, its mover having lost a phrase where the
smuggler carries one, and [no smuggler is a remnant of what it
carries](##Minimalist.SyntacticObject.Smuggles.not_isRemnantOf).

## Implementation notes

* Blocking is the blocker's c-command of the smugglee, which covers an intervener and not a
  barrier or a phase boundary. The relation blocked, and the probe that reaches the smugglee
  afterwards, are the consumer's to supply.

## References

* [collins-2005]
* [muller-1998]
-/

@[expose] public section

namespace Minimalist.SyntacticObject

variable {T m t xp w : SyntacticObject}

/-- Moving `m` to the root of `T`, leaving `t` in its place, smuggles `xp` past `w`. -/
structure Smuggles (T m t xp w : SyntacticObject) : Prop where
  /-- The smuggler contains the smugglee. -/
  contains : Contains m xp
  /-- The blocker c-commands the smugglee before the movement. -/
  blocked : CCommands T w xp
  /-- The smuggler c-commands the blocker after it. -/
  cCommands : CCommands (merge (T.replace m t) m) m w

/-- Smuggling works: the blocker no longer c-commands the smugglee after the movement, when no
token of the remainder is pronounced in the smuggler as well and neither is a bare trace. -/
theorem Smuggles.not_cCommands (h : Smuggles T m t xp w)
    (hd : Disjoint (T.replace m t).yield m.yield) (hxp : xp.yield ≠ 0) (hw : w.yield ≠ 0) :
    ¬ CCommands (merge (T.replace m t) m) w xp := by
  have key {u : SyntacticObject} (hu : u.yield ≠ 0) (hR : u ∈ (T.replace m t).terms)
      (hm : u ∈ m.terms) : False :=
    let ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hu
    Multiset.disjoint_left.1 hd (Multiset.mem_of_le (yield_le_of_mem_terms hR) ha)
      (Multiset.mem_of_le (yield_le_of_mem_terms hm) ha)
  have hxm : xp ∈ m.terms := mem_terms.2 h.contains.to_reflTransGen
  have hm0 : m.yield ≠ 0 := fun h ↦ hxp (Multiset.le_zero.1 (h ▸ yield_le_of_mem_terms hxm))
  have hparent {root x z : SyntacticObject} (h : Sisters root x z) : Contains root x :=
    let ⟨_, hy, hyx, _, _⟩ := h
    Relation.TransGen.tail' (mem_terms.1 hy) hyx
  have hwR : w ∈ (T.replace m t).terms := by
    obtain ⟨z, -, hs, hzw⟩ := h.cCommands
    rcases Sisters.of_merge hs with h | h | ⟨h, -⟩ | ⟨-, rfl⟩
    · exact (key hm0 h.mem_left (self_mem_terms m)).elim
    · exact (contains_irrefl m (hparent h)).elim
    · exact (key hm0 (h ▸ self_mem_terms m) (self_mem_terms m)).elim
    · exact mem_terms.2 hzw
  have hwm : w ∉ m.terms := key hw hwR
  have hmw' : m ∉ w.terms := fun h ↦
    key hm0 (terms_subset_terms (mem_terms.1 hwR) h) (self_mem_terms m)
  obtain ⟨z, -, hs, -⟩ := h.blocked
  rw [merge_comm]
  exact not_cCommands_merge_of_notMem_terms hwm
    (contains_iff_containsOrEq_and_ne.1 ((hparent hs).replace hwm hmw')).2 (key hxp · hxm)

/-- The smuggler is no remnant of what the smugglee pronounces. -/
theorem Smuggles.not_isRemnantOf (h : Smuggles T m t xp w) {tok : LexicalItem.Token}
    (ht : tok ∈ xp.yield) : ¬ m.IsRemnantOf tok :=
  fun hr ↦ hr.2 <| Multiset.mem_of_le
    (yield_le_of_mem_terms (mem_terms.2 h.contains.to_reflTransGen)) ht

end Minimalist.SyntacticObject

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

/-- A smuggling step is a smuggling movement at its stage of the derivation. -/
theorem IsSmugglingStep.smuggles (h : d.IsSmugglingStep i xp w) :
    ∃ m ∈ d.mover? i, (d.stageAt i).Smuggles m (m.headTrace selHead) xp w := by
  obtain ⟨m, hm, hmx, hwx, hmw⟩ := h
  obtain ⟨step, hs, hsm⟩ := Option.bind_eq_some_iff.1 hm
  have hstage : d.stageAt (i + 1) = (step.run (d.take i).run).current :=
    congrArg Cfg.current (run_take_succ hs)
  exact ⟨m, hm, hmx, hwx.cCommands_stageAt, (hstage ▸ hmw.cCommands_stageAt).mono
    (Step.terms_current_run_subset (τ := selHead) hsm (d.take i).run)⟩

/-- In a valid derivation the blocker no longer c-commands the smugglee after a smuggling step,
neither being a bare trace. -/
theorem IsSmugglingStep.not_cCommandsAt_succ (h : d.IsSmugglingStep i xp w)
    (hv : d.IsValid) (hxp : xp.yield ≠ 0) (hw : w.yield ≠ 0) :
    ¬ d.CCommandsAt (i + 1) w xp := by
  obtain ⟨m, hm, hsm⟩ := h.smuggles
  obtain ⟨step, hs, hstep⟩ := Option.bind_eq_some_iff.1 hm
  have hnd := run_take_succ hs ▸ hv.nodup_yield_run_take (i + 1)
  have hstage : d.stageAt (i + 1) = (step.run (d.take i).run).current :=
    congrArg Cfg.current (run_take_succ hs)
  have hdisj := (Multiset.nodup_add.1 <|
    Multiset.nodup_of_le (Step.yield_add_yield_le_yield_run hstep _) hnd).2.2
  exact fun hc ↦ hsm.not_cCommands hdisj hxp hw
    ((hstage ▸ hc.cCommands_stageAt).mono (Step.terms_current_run_subset hstep _))

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
    (ht : t ∈ xp.yield) : ¬ d.IsRemnantStep i t :=
  let ⟨_, hm, hs⟩ := h.smuggles
  fun ⟨_, hm', hr⟩ ↦ hs.not_isRemnantOf ht (Option.mem_unique hm' hm ▸ hr)

end Minimalist.Derivation
