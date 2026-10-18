/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Semantics.Denotation
public import Linglib.Semantics.Reference.Nominal
public import Linglib.Semantics.Presupposition.PhiFeatures
public import Linglib.Semantics.Composition.Assignment

/-!
# The denotation of a pronoun

This file defines the denotation of a personal pronoun. A `PersonalPronoun` entry denotes a
`Nominal` whose selector is the variable denotation `interpPronoun`, the value of the entry's
index under the assignment, and whose intrinsic presupposition is that the resolved referent lies
in the entry's φ-domain (`PersonalPronoun.phiDom`, `PersonalPronoun.denote`). The φ-domain is the
intersection of `Person.dom` at the context of utterance with `Number.dom` and `Gender.dom` at the
entry's referential person and number and its gender. The selector does not vary with the world
of evaluation (`PersonalPronoun.isRigid_denote_selector`), so a pronoun refers directly. This is
the account Büring surveys: one denotation serves the bound, anaphoric and deictic uses, binding
is abstraction over the assignment (`Montague.lambdaAbsG`), and, as Sauerland
proposes, an absent or unmarked feature restricts nothing.

## Implementation notes

The φ-domain reads the entry's referential person and number
(`PersonalPronoun.referentialPerson`, `PersonalPronoun.referentialNumber`), not its agreement
features, so a polite pronoun that agrees as third plural presupposes its addressee
(`PersonalPronoun.phiDom_congr`). The speaker and the addressee are the agent and the addressee
of the context of utterance (`Reference.Context`), and the female and the inanimate referents
are the gender of referents the entity domain comes equipped with (`Gendered`).

## References

* [buring-2012]
* [sauerland-2003]
-/

@[expose] public section

open Reference

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

/-- The φ-domain depends on the referential categories and the gender alone, not on the
agreement person and number. -/
theorem phiDom_congr {e₁ e₂ : PersonalPronoun} (hr : e₁.referential = e₂.referential)
    (hg : e₁.gender = e₂.gender) : e₁.phiDom c = e₂.phiDom c := by
  simp only [phiDom, referentialPerson, referentialNumber, hr, hg]

/-- A pronoun denotes the nominal whose selector is the variable denotation `interpPronoun i`,
always defined under a total assignment, and whose intrinsic presupposition is that the resolved
referent `g i` lies in the φ-domain. -/
def denote : Nominal (Assignment E) W E where
  presup g _ := g i ∈ e.phiDom c
  selector g _ := some (Montague.interpPronoun i g)

universe u

/-- A personal pronoun denotes on every model, the index and the context being the Reader
arguments of its domain. -/
instance : Semantics.Denotes PersonalPronoun
    (∀ (E W P T : Type u) [PartialOrder E] [Gendered E], ℕ → Context W E P T →
      Nominal (Assignment E) W E) :=
  ⟨fun e _ _ _ _ _ _ ↦ e.denote⟩

@[simp] theorem denote_presup (g : Assignment E) (w : W) :
    (e.denote i c).presup g w = (g i ∈ e.phiDom c) :=
  rfl

@[simp] theorem denote_selector (g : Assignment E) (w : W) :
    (e.denote i c).selector g w = some (g i) :=
  rfl

/-- A pronoun's selector is rigid, so its referent does not vary with the world. -/
theorem isRigid_denote_selector (g : Assignment E) :
    IsRigid ((e.denote i c).selector g) :=
  isRigid_const _

end PersonalPronoun
