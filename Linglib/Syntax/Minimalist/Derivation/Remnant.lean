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

A *remnant* is a constituent that something has moved out of, and *remnant movement* moves it
afterwards, so that what moves carries a trace whose antecedent lies outside it: a VP fronted after
its object has scrambled away, a predicate cleft fronting the VP after the verb has raised, VoiceP
raising after its subject has left. A trace remembers the head of the phrase that left it, so step
`i` of a derivation moves a remnant of the phrase headed by `h` when its mover holds a trace of `h`
but does not pronounce `h`. A mover that carried the phrase along, as when the phrase moved only to
the mover's own edge, pronounces `h` and is no remnant of it.

## Main definitions

* `Minimalist.Derivation.IsRemnantStep`: step `i` of a derivation moves a remnant of the phrase
  headed by `h`.

## Implementation notes

* The evacuee is named by its head token, as chains are in `Copy/Chain.lean`. In a derivation that
  merges each token once, the antecedent of a trace of `h` lies outside the mover exactly when the
  mover does not pronounce `h`, whatever was later extracted from the evacuee itself.
* Whether the lower copy of the evacuee inside the remnant is pronounced, as in the verb doubling
  of predicate clefts, is a question of chain pronunciation that a derivation, which pronounces no
  trace, leaves open.

## TODO

* After a remnant step that lands above the evacuee, the trace of `h` has no antecedent in the
  surface object, an orphan trace of `Copy/Chain.lean`; state and prove this.

## References

* [hinterholzl-2006]
* [koopman-1997]
* [aboh-dyakonova-2009]
* [van-urk-2024]
* [landau-2006]
* [harizanov-gribanova-2017]
* [cole-hermon-2008]
* [sande-clem-dabkowski-2026]
-/

@[expose] public section

namespace Minimalist.Derivation

open SyntacticObject

variable {d : Derivation} {steps : List Step} {i : Nat} {h : LexicalItem.Token}

/-- Step `i` of `d` moves a remnant of the phrase headed by `h`: its mover holds a trace of `h` but
does not pronounce `h`. -/
def IsRemnantStep (d : Derivation) (i : Nat) (h : LexicalItem.Token) : Prop :=
  ∃ m ∈ d.mover? i, traceOf h ∈ m.terms ∧ h ∉ m.yield

instance (d : Derivation) (i : Nat) (h : LexicalItem.Token) : Decidable (d.IsRemnantStep i h) :=
  inferInstanceAs (Decidable (∃ m ∈ d.mover? i, _))

theorem IsRemnantStep.lt_length (hr : d.IsRemnantStep i h) : i < d.length :=
  let ⟨_, hm, _⟩ := hr
  lt_length_of_mem_mover? hm

theorem isRemnantStep_append_of_lt (hi : i < d.length) :
    (d.append steps).IsRemnantStep i h ↔ d.IsRemnantStep i h := by
  rw [IsRemnantStep, IsRemnantStep, mover?_append_of_lt hi]

theorem IsRemnantStep.append (hr : d.IsRemnantStep i h) : (d.append steps).IsRemnantStep i h :=
  (isRemnantStep_append_of_lt hr.lt_length).2 hr

theorem isRemnantStep_map_iff {f : LexicalItem.Token → LexicalItem.Token}
    (hf : Function.Injective f) : (d.map f).IsRemnantStep i (f h) ↔ d.IsRemnantStep i h := by
  have hmem (m x : SyntacticObject) : x.map f ∈ (m.map f).terms ↔ x ∈ m.terms := by
    rw [terms_map, Multiset.mem_map_of_injective (map_injective hf)]
  cases hm : d.mover? i with
  | none => simp [IsRemnantStep, mover?_map, hm]
  | some m =>
    simp only [IsRemnantStep, mover?_map, hm, Option.map_some, Option.mem_def, Option.some.injEq,
      exists_eq_left', mem_yield_iff]
    rw [← map_traceOf, ← map_leaf, hmem, hmem]

end Minimalist.Derivation
