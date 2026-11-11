/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.CCommand
public import Linglib.Syntax.Minimalist.Derivation.Freezing
public import Linglib.Syntax.Minimalist.Derivation.Movement
public import Linglib.Syntax.Minimalist.Derivation.Remnant

/-!
# Smuggling

A phrase that a blocker keeps out of reach can be carried past the blocker inside a larger one.
The smuggler YP *smuggles* the smugglee XP past the blocker W when YP contains XP, W blocks a
relation between XP and something higher, and YP moves to a position c-commanding W. This is a
property of one movement, `Movement.Smuggles`, and [the blocker no longer c-commands the smugglee
after it](##Minimalist.Movement.Smuggles.not_cCommands) when the source pronounces no token twice,
as in [a valid derivation](##Minimalist.Derivation.IsSmugglingStep.not_cCommandsAt_succ).
`Derivation.IsSmugglingStep` says that the movement of a step smuggles. The step [freezes the
smugglee](##Minimalist.Derivation.IsSmugglingStep.frozen), so [a derivation that goes on to move it
violates Freezing](##Minimalist.Derivation.IsSmugglingStep.not_obeysFreezing), which smuggling
accounts must lift. Remnant movement is the converse, its mover having lost a phrase where the
smuggler carries one, and [no smuggler is a remnant of what it
carries](##Minimalist.Movement.Smuggles.not_isRemnantOf).

## Implementation notes

* Blocking is the blocker's c-command of the smugglee, which covers an intervener and not a
  barrier or a phase boundary. The relation blocked, and the probe that reaches the smugglee
  afterwards, are the consumer's to supply.

## References

* [collins-2005]
* [muller-1998]
-/

@[expose] public section

namespace Minimalist.Movement

open SyntacticObject

variable {μ : Movement} {τ : SyntacticObject → Option LexicalItem.Token} {xp w : SyntacticObject}

/-- The movement smuggles `xp` past `w`. -/
@[mk_iff]
structure Smuggles (μ : Movement) (xp w : SyntacticObject)
    (τ : SyntacticObject → Option LexicalItem.Token := selHead) : Prop where
  /-- The smuggler contains the smugglee. -/
  contains : Contains μ.mover xp
  /-- The blocker c-commands the smugglee before the movement. -/
  blocked : CCommands μ.source w xp
  /-- The smuggler c-commands the blocker after it. -/
  cCommands : CCommands (μ.result τ) μ.mover w

instance : Decidable (μ.Smuggles xp w τ) := decidable_of_iff _ (smuggles_iff μ xp w τ).symm

/-- Smuggling works: the blocker no longer c-commands the smugglee after the movement, when the
source pronounces no token twice and neither is a bare trace. -/
theorem Smuggles.not_cCommands (h : μ.Smuggles xp w τ) (hs : μ.source.yield.Nodup)
    (hxp : xp.yield ≠ 0) (hw : w.yield ≠ 0) : ¬ CCommands (μ.result τ) w xp := by
  have hd := disjoint_yield τ hs
  show ¬ CCommands (merge (μ.remainder τ) μ.mover) w xp
  have key {u : SyntacticObject} (hu : u.yield ≠ 0) (hR : u ∈ (μ.remainder τ).terms)
      (hm : u ∈ μ.mover.terms) : False :=
    let ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hu
    Multiset.disjoint_left.1 hd (Multiset.mem_of_le (yield_le_of_mem_terms hR) ha)
      (Multiset.mem_of_le (yield_le_of_mem_terms hm) ha)
  have hxm : xp ∈ μ.mover.terms := mem_terms.2 h.contains.to_reflTransGen
  have hm0 : μ.mover.yield ≠ 0 := fun h ↦ hxp (Multiset.le_zero.1 (h ▸ yield_le_of_mem_terms hxm))
  have hparent {root x z : SyntacticObject} (h : Sisters root x z) : Contains root x :=
    let ⟨_, hy, hyx, _, _⟩ := h
    Relation.TransGen.tail' (mem_terms.1 hy) hyx
  have hwR : w ∈ (μ.remainder τ).terms := by
    obtain ⟨z, -, hs, hzw⟩ := h.cCommands
    rcases Sisters.of_merge hs with h | h | ⟨h, -⟩ | ⟨-, rfl⟩
    · exact (key hm0 h.mem_left (self_mem_terms μ.mover)).elim
    · exact (contains_irrefl μ.mover (hparent h)).elim
    · exact (key hm0 (h ▸ self_mem_terms μ.mover) (self_mem_terms μ.mover)).elim
    · exact mem_terms.2 hzw
  have hwm : w ∉ μ.mover.terms := key hw hwR
  have hmw' : μ.mover ∉ w.terms := fun h ↦
    key hm0 (terms_subset_terms (mem_terms.1 hwR) h) (self_mem_terms μ.mover)
  obtain ⟨z, -, hs, -⟩ := h.blocked
  rw [merge_comm]
  exact not_cCommands_merge_of_notMem_terms hwm
    (contains_iff_containsOrEq_and_ne.1 ((hparent hs).replace hwm hmw')).2 (key hxp · hxm)

/-- The smuggler is no remnant of what the smugglee pronounces. -/
theorem Smuggles.not_isRemnantOf (h : μ.Smuggles xp w τ) {tok : LexicalItem.Token}
    (ht : tok ∈ xp.yield) : ¬ μ.mover.IsRemnantOf tok :=
  fun hr ↦ hr.2 <| Multiset.mem_of_le
    (yield_le_of_mem_terms (mem_terms.2 h.contains.to_reflTransGen)) ht

end Minimalist.Movement

namespace Minimalist.Derivation

open SyntacticObject

variable {d : Derivation} {steps : List Step} {i j : Nat} {xp w : SyntacticObject}

/-- Step `i` of `d` smuggles `xp` past `w`: its movement does. -/
def IsSmugglingStep (d : Derivation) (i : Nat) (xp w : SyntacticObject) : Prop :=
  ∃ μ ∈ d.movement? i, μ.Smuggles xp w

/-- A smuggling step in terms of its mover and its stage. -/
theorem isSmugglingStep_iff :
    d.IsSmugglingStep i xp w ↔ ∃ m ∈ d.mover? i, Contains (d.stageAt i) m ∧ Contains m xp ∧
      CCommands (d.stageAt i) w xp ∧
        CCommands (merge (deleteAccessible m (d.stageAt i)) m) m w := by
  constructor
  · rintro ⟨μ, hμ, hs⟩
    obtain ⟨hm, hsrc⟩ := mem_movement?_iff.1 hμ
    exact ⟨μ.mover, hm, hsrc ▸ μ.contains, hs.contains, hsrc ▸ hs.blocked, hsrc ▸ hs.cCommands⟩
  · rintro ⟨m, hm, hc, hmx, hwx, hmw⟩
    exact ⟨⟨d.stageAt i, m, hc⟩, mem_movement?_iff.2 ⟨hm, rfl⟩, hmx, hwx, hmw⟩

instance (d : Derivation) (i : Nat) (xp w : SyntacticObject) :
    Decidable (d.IsSmugglingStep i xp w) :=
  decidable_of_iff _ isSmugglingStep_iff.symm

theorem IsSmugglingStep.lt_length (h : d.IsSmugglingStep i xp w) : i < d.length :=
  let ⟨_, hμ, _⟩ := h
  lt_length_of_mem_movement? hμ

theorem isSmugglingStep_append_of_lt (hi : i < d.length) :
    (d.append steps).IsSmugglingStep i xp w ↔ d.IsSmugglingStep i xp w := by
  rw [IsSmugglingStep, IsSmugglingStep, movement?_append_of_lt hi]

theorem IsSmugglingStep.append (h : d.IsSmugglingStep i xp w) :
    (d.append steps).IsSmugglingStep i xp w :=
  (isSmugglingStep_append_of_lt h.lt_length).2 h

theorem isSmugglingStep_map_iff {f : LexicalItem.Token → LexicalItem.Token}
    (hf : Function.Injective f) (hsel : LexicalItem.Token.PreservesSelection f) :
    (d.map f).IsSmugglingStep i (xp.map f) (w.map f) ↔ d.IsSmugglingStep i xp w := by
  have hτ : ∀ s : SyntacticObject, selHead (s.map f) = (selHead s).map f :=
    fun s ↦ s.selHead_map hsel
  rw [isSmugglingStep_iff, isSmugglingStep_iff]
  cases h : d.mover? i <;>
    simp [mover?_map, h, stageAt_map d hf hτ, contains_map_iff hf, cCommands_map_iff hf,
      deleteAccessible, ← replace_map hf, ← SyntacticObject.headTrace_map hτ, ← map_merge]

/-- In a valid derivation the blocker no longer c-commands the smugglee after a smuggling step,
neither being a bare trace. -/
theorem IsSmugglingStep.not_cCommandsAt_succ (h : d.IsSmugglingStep i xp w)
    (hv : d.IsValid) (hxp : xp.yield ≠ 0) (hw : w.yield ≠ 0) :
    ¬ d.CCommandsAt (i + 1) w xp := by
  obtain ⟨μ, hμ, hs⟩ := h
  obtain ⟨hm, hsrc⟩ := mem_movement?_iff.1 hμ
  obtain ⟨step, hstep, hmv⟩ := Option.bind_eq_some_iff.1 hm
  have hnd : μ.source.yield.Nodup := hsrc ▸
    Multiset.nodup_of_le (Multiset.le_add_right _ _) (hv.nodup_yield_run_take i)
  have hstage : d.stageAt (i + 1) = (step.run (d.take i).run).current :=
    congrArg Cfg.current (run_take_succ hstep)
  intro hc
  have := (hstage ▸ hc.cCommands_stageAt).mono (Step.terms_current_run_subset hmv _)
  exact hs.not_cCommands hnd hxp hw (by
    rw [Movement.result, Movement.remainder, hsrc]; exact this)

/-- A smuggling step freezes what it smuggles. -/
theorem IsSmugglingStep.frozen (h : d.IsSmugglingStep i xp w) : d.Frozen xp :=
  let ⟨μ, hμ, hs⟩ := h
  ⟨μ.mover, mem_movedItems_of_mem_mover? (mem_movement?_iff.1 hμ).1, hs.contains⟩

/-- A derivation that smuggles a phrase and goes on to move it violates Freezing. -/
theorem IsSmugglingStep.not_obeysFreezing (h : d.IsSmugglingStep i xp w) (hij : i < j)
    (hj : xp ∈ d.mover? j) : ¬ d.ObeysFreezing :=
  let ⟨μ, hμ, hs⟩ := h
  fun hf ↦ obeysFreezing_iff_forall_mover?.1 hf hij μ.mover (mem_movement?_iff.1 hμ).1 xp hj
    hs.contains

/-- A step does not move a remnant of what the phrase it smuggles pronounces. -/
theorem IsSmugglingStep.not_isRemnantStep (h : d.IsSmugglingStep i xp w) {t : LexicalItem.Token}
    (ht : t ∈ xp.yield) : ¬ d.IsRemnantStep i t :=
  let ⟨_, hμ, hs⟩ := h
  fun ⟨_, hm', hr⟩ ↦
    hs.not_isRemnantOf ht (Option.mem_unique hm' (mem_movement?_iff.1 hμ).1 ▸ hr)

end Minimalist.Derivation
