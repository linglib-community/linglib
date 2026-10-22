/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Linearization.Cyclic
public import Linglib.Syntax.Minimalist.Linearization.Replay

/-!
# Spell-out domains of a derivation

A Spell-out domain in the sense of [fox-pesetsky-2005] is a constituent the derivation has built,
linearized when Spell-out applies to it. On a derivation the constituent built by the first `m`
steps is the ordered object of that stage, and at a later stage `n` it stands inside the larger
object with whatever has moved out of it in between replaced by traces
(`Derivation.spelloutDomain`). Its Spell-out at `n` is its pronounced yield
(`Derivation.spellout`), so the Spell-out snapshots that cyclic linearization reads
(`Linearization/Cyclic.lean`) come from the derivation itself, and a derivation linearizes under a
schedule of Spell-outs when those snapshots cohere (`Derivation.Linearizes`).

Fox and Pesetsky spell a domain out when it is built, which reads the surface of its stage
(`Derivation.spellout_self`); spelling a phase out when the next phase head merges, as Chomsky
proposes, takes the stage after that merge (`Derivation.mergeStage?`). Which constituent a study
spells out, the whole phase or the head with its complement, is the stage it names. A head moved
into a phase head by Internal Merge stays inside the constituent the two build, so the moved verb
of a verb-plus-v head is spelled out with v.

## Main definitions

* `Minimalist.Derivation.spelloutDomain`, `Derivation.spellout`: a domain at a
  later stage, and its Spell-out.
* `Minimalist.Derivation.Linearizes`: a derivation linearizes under a schedule.

## Main statements

* `Minimalist.Derivation.spellout_self`: a domain spelled out when it is built
  reads the surface of its stage.
* `Minimalist.Derivation.spellout_append_of_le`: extending a derivation changes
  no earlier Spell-out.

## References

* [fox-pesetsky-2005]
* [chomsky-2001]
-/

@[expose] public section

namespace Minimalist

open SyntacticObject

/-- Inside a constituent built earlier, External Merge and merging back do nothing, and Internal
Merge and extraction replace the mover by its trace, unless the constituent is itself the mover,
which then moves intact. -/
def Step.applyInside (step : Step) (D : LinearizedSyntacticObject) : LinearizedSyntacticObject :=
  match step with
  | .em _ _ | .remerge _ => D
  | .im mover _ | .extract mover =>
    if D.toSyntacticObject = mover then D
    else D.replace mover mover.traceLinearized

namespace Derivation

variable (d : Derivation) (m n : ℕ)

/-- `d.stage? n` is the ordered object after the first `n` steps, if the replay succeeds. -/
def stage? : Option LinearizedSyntacticObject := (d.take n).externalize?

/-- The constituent built by the first `m` steps stands at stage `n` with the movers of the steps
in between replaced by their traces. -/
def spelloutDomain : Option LinearizedSyntacticObject :=
  (d.stage? m).map fun D ↦ ((d.steps.drop m).take (n - m)).foldl (fun D step ↦ step.applyInside D) D

/-- The Spell-out at stage `n` of the domain built by stage `m` is its pronounced yield. -/
def spellout : List LexicalItem.Token := ((d.spelloutDomain m n).map (·.yield)).getD []

/-- `d.mergeStage? item` is the stage right after `item` is externally merged, if it is. -/
def mergeStage? (item : SyntacticObject) : Option ℕ :=
  (d.steps.findIdx? fun step ↦ match step with
    | .em _ x => decide (x = item)
    | _ => false).map (· + 1)

/-- A derivation linearizes under a schedule of Spell-outs, each the stage at which a domain is
built and the stage at which it is spelled out, when their snapshots cohere. -/
def Linearizes (sched : List (ℕ × ℕ)) : Prop :=
  Linearization.Consistent (sched.map fun p ↦ d.spellout p.1 p.2)

instance (sched : List (ℕ × ℕ)) : Decidable (d.Linearizes sched) :=
  inferInstanceAs (Decidable (Linearization.Consistent _))

variable {d m n} {steps : List Step}

@[simp] theorem spelloutDomain_self : d.spelloutDomain m m = d.stage? m := by
  simp [spelloutDomain]

/-- A domain spelled out when it is built reads the surface of its stage. -/
theorem spellout_self : d.spellout m m = (d.take m).surfaceTokens := by
  simp [spellout, stage?, surfaceTokens]

theorem stage?_append_of_le (h : n ≤ d.length) : (d.append steps).stage? n = d.stage? n := by
  rw [stage?, stage?, take_append_of_le h]

theorem spelloutDomain_append_of_le (hmn : m ≤ n) (h : n ≤ d.length) :
    (d.append steps).spelloutDomain m n = d.spelloutDomain m n := by
  rw [spelloutDomain, spelloutDomain, stage?_append_of_le (hmn.trans h)]
  congr 2
  rw [append, List.drop_append_of_le_length (hmn.trans h),
    List.take_append_of_le_length (by rw [List.length_drop]; simp only [length] at h; omega)]

/-- Extending a derivation changes no earlier Spell-out. -/
theorem spellout_append_of_le (hmn : m ≤ n) (h : n ≤ d.length) :
    (d.append steps).spellout m n = d.spellout m n := by
  rw [spellout, spellout, spelloutDomain_append_of_le hmn h]

/-- A linearizing derivation spells no domain out with a repeated token. -/
theorem Linearizes.nodup {sched : List (ℕ × ℕ)} (h : d.Linearizes sched) {p : ℕ × ℕ}
    (hp : p ∈ sched) : (d.spellout p.1 p.2).Nodup :=
  Linearization.Consistent.nodup h (List.mem_map_of_mem hp)

end Derivation

end Minimalist
