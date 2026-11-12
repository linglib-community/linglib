/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Reference.Definite
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Logic.Assignment

/-!
# The denotation of a pronoun

This file defines the denotation of a personal pronoun. A `PersonalPronoun` entry denotes the
`Definite` that is the value of the entry's index under the assignment where that value lies in
the entry's φ-domain, and nothing elsewhere (`PersonalPronoun.phiDom`, `PersonalPronoun.denote`).
The φ-domain is the intersection of `Person.dom` at the context of utterance with `Number.dom`
and `Gender.dom` at the entry's referential person and number and its gender. The denotation
does not vary with the world of evaluation (`PersonalPronoun.isRigid_denote`), so a pronoun
refers directly. This is the account Büring surveys: one denotation serves the bound, anaphoric
and deictic uses, binding is abstraction over the assignment (`Λ[n]`), and, as Sauerland
proposes, an absent or unmarked feature restricts nothing.

## Implementation notes

The φ-domain reads the entry's referential person and number
(`PersonalPronoun.referentialPerson`, `PersonalPronoun.referentialNumber`), not its agreement
features, so a polite pronoun that agrees as third plural presupposes its addressee
(`PersonalPronoun.phiDom_congr`). The speaker and the addressee are the agent and the addressee
of the context of utterance (`Kaplan.Context`), and the female and the inanimate referents
are the gender of referents the entity domain comes equipped with (`Gendered`).

## References

* [buring-2012]
* [sauerland-2003]
-/

@[expose] public section

open Kaplan

namespace PersonalPronoun

variable {E W P T : Type*} [PartialOrder E] [Gendered E] (e : PersonalPronoun) (i : ℕ)
  (c : Context W E P T)

/-- The φ-domain of a pronoun entry over an entity domain `E` is the intersection of the person
domain of its referential person at the context of utterance, the number domain of its referential
number and the gender domain of its gender. -/
def phiDom : Set E :=
  Person.dom c e.referentialPerson ∩
    Number.dom e.referentialNumber ∩
    Gender.dom e.gender

@[simp] theorem mem_phiDom (x : E) :
    x ∈ e.phiDom c ↔
      x ∈ Person.dom c e.referentialPerson ∧ x ∈ Number.dom e.referentialNumber ∧
        x ∈ Gender.dom e.gender := by
  simp only [phiDom, Set.mem_inter_iff, and_assoc]

theorem phiDom_congr {e₁ e₂ : PersonalPronoun} (hr : e₁.referential = e₂.referential)
    (hg : e₁.gender = e₂.gender) : e₁.phiDom c = e₂.phiDom c := by
  simp only [phiDom, referentialPerson, referentialNumber, hr, hg]

/-- A pronoun denotes the value `g i` of its index where that value lies in the φ-domain, and
nothing elsewhere. -/
def denote : Definite (ℕ → E) W E := .var i (e.phiDom c)

universe u

/-- A personal pronoun denotes on every model, the index and the context being the Reader
arguments of its domain. -/
instance : Denotes PersonalPronoun
    (∀ (E W P T : Type u) [PartialOrder E] [Gendered E], ℕ → Context W E P T →
      Definite (ℕ → E) W E) :=
  ⟨fun e _ _ _ _ _ _ ↦ e.denote⟩

@[simp] theorem denote_dom (g : ℕ → E) (w : W) :
    (e.denote i c g w).Dom ↔ g i ∈ e.phiDom c :=
  Iff.rfl

@[simp] theorem mem_denote {g : ℕ → E} {w : W} {x : E} :
    x ∈ e.denote i c g w ↔ g i ∈ e.phiDom c ∧ g i = x :=
  Definite.mem_var

theorem isRigid_denote (g : ℕ → E) : IsRigid (e.denote (W := W) i c g) :=
  isRigid_const _

end PersonalPronoun
