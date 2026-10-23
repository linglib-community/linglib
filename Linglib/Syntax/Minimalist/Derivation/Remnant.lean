/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Minimalist.Derivation.Basic
public import Linglib.Syntax.Minimalist.SyntacticObject.Term

/-!
# Remnant movement

A constituent moves after part of it has moved out, so what fronts is a remnant carrying the
trace of what left it: [koopman-1997]'s predicate clefts in Vata and Nweh, where the VP fronts
after the verb has raised, the Gungbe and Kwa predicate doubling of [aboh-dyakonova-2009], the
constraints on predicate fronting [van-urk-2024] surveys, Toba Batak's VoiceP raising after the
goal and the subject have evacuated it ([cole-hermon-2008], `Studies/ColeHermon2008.lean`), and
Guébie's particle fronting after the verb has left the VP ([sande-clem-dabkowski-2026],
`Studies/SandeClemDabkowski2026.lean`). On a derivation
the notion is exact: step `i` fronts a remnant when its mover contains the trace the head of an
earlier mover left. Whether the evacuee's lower copy is pronounced inside the remnant, the verb
doubling of predicate clefts, is a matter of chain pronunciation, phonological for
[landau-2006] and syntactic for [koopman-1997] and [harizanov-gribanova-2017]; the carrier
pronounces no trace and does not decide it. Remnant movement is the converse of smuggling
(`Derivation/Smuggling.lean`, [collins-2005]), in which the larger constituent moves with the
smaller one still inside it.

## Main definitions

* `Minimalist.Derivation.IsRemnantStep`

## Main results

* `Minimalist.Derivation.IsRemnantStep.append`: a remnant step of a derivation
  is one of every extension.

## References

* [koopman-1997]
* [aboh-dyakonova-2009]
* [van-urk-2024]
* [landau-2006]
* [harizanov-gribanova-2017]
* [collins-2005]
* [cole-hermon-2008]
* [sande-clem-dabkowski-2026]
-/

@[expose] public section

namespace Minimalist.Derivation

open SyntacticObject

variable {d : Derivation} {steps : List Step} {i : Nat}

/-- Step `i` of `d` fronts a remnant: its mover contains the trace left by an earlier mover. -/
def IsRemnantStep (d : Derivation) (i : Nat) : Prop :=
  ∃ m ∈ d.mover? i, ∃ x ∈ (d.take i).movedItems, Contains m x.headTrace

instance (d : Derivation) (i : Nat) : Decidable (d.IsRemnantStep i) := by
  unfold IsRemnantStep; infer_instance

/-- A remnant step of a derivation is one of every extension. -/
theorem IsRemnantStep.append (h : d.IsRemnantStep i) : (d.append steps).IsRemnantStep i := by
  obtain ⟨m, hm, x, hx, hc⟩ := h
  have hi := lt_length_of_mem_mover? hm
  exact ⟨m, by rwa [mover?_append_of_lt hi], x, by rwa [take_append_of_le hi.le], hc⟩

end Minimalist.Derivation
