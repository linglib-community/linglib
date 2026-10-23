module

public import Linglib.Fragments.English.Pronouns
public import Linglib.Semantics.Reference.Pronoun

/-!
# Büring (2012): Pronouns

This file formalizes the semantics of definite pronouns in Büring's handbook survey, as theorems
about the project's pronoun denotation applied to the English Fragment's entries. A pronoun is
indexed and denotes the value its index has under the assignment; bound, anaphoric and deictic uses
share that one denotation, so a binder is an external operator manipulating the assignment rather
than a second lexical entry. The φ-features are presuppositions on the resolved referent: *she*
picks out the assignment value only when that value is singular and not gendered masculine, *I*
only when it includes the agent of the context, and each is undefined, neither true nor false,
merely infelicitous, otherwise. The unmarked feature values contribute nothing, so a pronoun that
carries only unmarked values is defined of any referent at all. That is the survey's
underspecification treatment of *they*, whose gender-neutrality is the absence of a gender
feature rather than a feature of its own.

## Main results

* `selector_eq_assignment`: a pronoun denotes the assignment value at its index.
* `undefined_of_masculine`, `undefined_of_not_agent`: a feminine entry is undefined of a
  referent gendered masculine, a first-person entry of one not including the agent.
* `defined_of_unmarked_features`: an entry with only unmarked values imposes no condition.
* `they_defined_where_she_undefined`: the two English entries at a male referent.
* `bound_reading`: binding is an assignment update, with the entry's denotation unchanged.

## References

* [D. Büring, *Pronouns* (2012)][buring-2012]
* [U. Sauerland, *A new semantics for number* (2003)][sauerland-2003]
-/

@[expose] public section

namespace Buring2012

open English.Pronouns

variable {E P T : Type*} [PartialOrder E] [Gendered E] (e : PersonalPronoun) (g : Assignment E)
  (n : ℕ) (c : Kaplan.Context PUnit E P T) (scope : E → PUnit → Prop)

theorem selector_eq_assignment :
    (e.denote n c).selector g ⟨⟩
      = some (g n) := rfl

theorem undefined_of_masculine (hfem : e.gender = some .feminine) (h : g n ∈ Gendered.masculine) :
    (e.denote n c).toTrivalent scope g ⟨⟩ = 0 := by
  simp [hfem, h]

theorem she_undefined_of_masculine (h : g n ∈ Gendered.masculine) :
    (she.denote n c).toTrivalent scope g ⟨⟩ = 0 :=
  undefined_of_masculine she g n c scope rfl h

theorem undefined_of_not_agent (hp : e.referentialPerson = some .first) (h : ¬ c.agent ≤ g n) :
    (e.denote n c).toTrivalent scope g ⟨⟩ = 0 := by
  simp [hp, h]

theorem i_undefined_of_not_agent (h : ¬ c.agent ≤ g n) :
    (i.denote n c).toTrivalent scope g ⟨⟩ = 0 :=
  undefined_of_not_agent i g n c scope (by decide) h

theorem defined_of_unmarked_features (hp : e.referentialPerson = some .third)
    (hn : e.referentialNumber = some .plural) (hg : e.gender = none) :
    (e.denote n c).toTrivalent scope g ⟨⟩ ≠ 0 := by
  simp [hp, hn, hg]

theorem they_defined_regardless_of_gender :
    (they.denote n c).toTrivalent scope g ⟨⟩ ≠ 0 :=
  defined_of_unmarked_features they g n c scope (by decide) (by decide) rfl

theorem they_defined_where_she_undefined (h : g n ∈ Gendered.masculine) :
    (she.denote n c).toTrivalent scope g ⟨⟩ = 0 ∧ (they.denote n c).toTrivalent scope g ⟨⟩ ≠ 0 :=
  ⟨she_undefined_of_masculine g n c scope h,
    they_defined_regardless_of_gender g n c scope⟩

theorem bound_reading (b : E) :
    (e.denote n c).selector (Function.update g n b) ⟨⟩ = some b := by
  simp

end Buring2012
