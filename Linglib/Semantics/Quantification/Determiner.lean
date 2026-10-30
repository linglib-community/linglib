/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Denotation

/-!
# The readings of a quantificational determiner

A quantificational determiner denotes the readings its entry records, each the global
denotation of a determiner symbol, so it has as many readings as symbols it records, and none
when its standard is left to context, as with *many*. Each symbol denotes the global
denotation of a tree of numbers, so every reading of every quantificational determiner is
[conservative, satisfies extension and is closed under
isomorphism](##QuantificationalDeterminer.conservative_ext_isom_of_mem_denote): what a lexical
entry can mean meets the conditions that determiner denotations are claimed to meet.

## References

* [barwise-cooper-1981]
* [keenan-stavi-1986]
* [van-benthem-1984]
* [peters-westerstahl-2006]
-/

@[expose] public section

universe u

open Quantifier
open scoped Denotes

namespace QuantificationalDeterminer

/-- A quantificational determiner denotes the denotations of its readings. -/
noncomputable instance : Denotes QuantificationalDeterminer (Set Det.Family.{u}) where
  denote d := (fun s : Det.Symbol ↦ s.denote) '' (d.readings : Set Det.Symbol)

variable {d : QuantificationalDeterminer} {Q : Det.Family.{u}}

theorem denote_def (d : QuantificationalDeterminer) :
    (⟦d⟧ : Set Det.Family.{u}) =
      (fun s : Det.Symbol ↦ s.denote) '' (d.readings : Set Det.Symbol) :=
  rfl

@[simp] theorem mem_denote_iff : Q ∈ ⟦d⟧ ↔ ∃ s ∈ d.readings, s.denote = Q := Iff.rfl

theorem denote_mem_denote {s : Det.Symbol} (hs : s ∈ d.readings) :
    (s.denote : Det.Family.{u}) ∈ ⟦d⟧ :=
  ⟨s, hs, rfl⟩

/-- Every reading of a quantificational determiner is conservative, satisfies extension and is
closed under isomorphism. -/
theorem conservative_ext_isom_of_mem_denote (hQ : Q ∈ ⟦d⟧) :
    Q.Conservative ∧ Q.Ext ∧ Q.Isom := by
  obtain ⟨s, -, rfl⟩ := mem_denote_iff.1 hQ
  exact ⟨s.conservative_denote, s.ext_denote, s.isom_denote⟩

end QuantificationalDeterminer
