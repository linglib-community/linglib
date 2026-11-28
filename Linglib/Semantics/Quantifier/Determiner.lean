/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Determiner.Basic
public import Linglib.Semantics.Quantifier.Global
public import Linglib.Semantics.Denotation

/-!
# The readings of a quantificational determiner

A quantificational determiner records a finite set of determiner symbols, its readings. This file
makes it denote the global determiner denotations of those symbols. A determiner whose standard is
left to context, such as *many*, records no symbol and denotes the empty set.

## Main results

* `QuantificationalDeterminer.ncard_denote`: a quantificational determiner has as many denotations
  as it records symbols.
* `QuantificationalDeterminer.conservative_ext_isom_of_mem_denote`: every denotation of a
  quantificational determiner is conservative, satisfies extension and is closed under isomorphism.

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

theorem denote_eq_singleton {s : Det.Symbol} (h : d.readings = {s}) :
    (⟦d⟧ : Set Det.Family.{u}) = {s.denote} := by
  rw [denote_def, h, Finset.coe_singleton, Set.image_singleton]

/-- A quantificational determiner has as many readings as the symbols its entry records. -/
theorem ncard_denote (d : QuantificationalDeterminer) :
    (⟦d⟧ : Set Det.Family.{u}).ncard = d.readings.card := by
  rw [denote_def, Set.ncard_image_of_injective _ Det.Symbol.denote_injective,
    Set.ncard_coe_finset]

/-- Every reading of a quantificational determiner is conservative, satisfies extension and is
closed under isomorphism. -/
theorem conservative_ext_isom_of_mem_denote (hQ : Q ∈ ⟦d⟧) :
    Q.Conservative ∧ Q.Ext ∧ Q.Isom := by
  obtain ⟨s, -, rfl⟩ := mem_denote_iff.1 hQ
  exact ⟨s.conservative_denote, s.ext_denote, s.isom_denote⟩

end QuantificationalDeterminer
