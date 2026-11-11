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
  obtain ⟨m, hm, hmx, ⟨p, hp, hwx⟩, q, hq, hmw⟩ := h
  rintro ⟨q', hq', hc⟩
  obtain rfl := Option.mem_unique hq hq'
  obtain ⟨step, hs, hsm⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨c, hc', rfl⟩ := Option.map_eq_some_iff.1 hq
  have hd' := Multiset.nodup_of_le (d.lexTokens_take_le (i + 1)) hd
  have hrun : (d.take (i + 1)).run = step.run (d.take i).run := by
    rw [take_succ hs, run_append]; rfl
  have hnd : (step.run (d.take i).run).yield.Nodup := by
    rwa [← hrun, ← replay?_faithful _ hc', yield_replay? hd' hc']
  have hcur : c.current.toSyntacticObject = (step.run (d.take i).run).current := by
    rw [← hrun, ← replay?_faithful _ hc']; rfl
  rw [externalize?_faithful _ hp, final] at hwx
  rw [hcur] at hmw hc
  generalize (d.take i).run = cfg at hwx hmw hc hnd
  obtain ⟨cur, st⟩ := cfg
  cases step with
  | em _ _ | remerge _ => cases hsm
  | im mover side =>
    obtain rfl : mover = m := Option.some.inj hsm
    refine not_cCommands_merge_replace (t := mover.headTrace selHead) ?_ hxp hw hmx hwx hmw hc
    exact (Multiset.nodup_add.1 <| Multiset.nodup_of_le
      ((Multiset.le_add_right _ (st.map yield).sum).trans_eq <| by
        simp [Cfg.yield, Step.run, Step.apply, deleteAccessible]) hnd).2.2
  | extract mover =>
    obtain rfl : mover = m := Option.some.inj hsm
    have hsub {x y : SyntacticObject}
        (h : CCommands (cur.replace mover (mover.headTrace selHead)) x y) :
        CCommands (merge (cur.replace mover (mover.headTrace selHead)) mover) x y :=
      h.mono fun u hu ↦ by
        rw [terms_merge]; exact Multiset.mem_cons_of_mem (Multiset.mem_add.2 (.inl hu))
    refine not_cCommands_merge_replace ?_ hxp hw hmx hwx (hsub hmw) (hsub hc)
    exact (Multiset.nodup_add.1 <| Multiset.nodup_of_le
      ((Multiset.le_add_right _ (st.map yield).sum).trans_eq <| by
        simp [Cfg.yield, Step.run, Step.apply, deleteAccessible, add_assoc]) hnd).2.2

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
