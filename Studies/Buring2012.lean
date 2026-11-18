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

## References

* [D. Büring, *Pronouns* (2012)][buring-2012]
* [U. Sauerland, *A new semantics for number* (2003)][sauerland-2003]
-/

public section

namespace Buring2012

open English.Pronouns

variable {E P T : Type*} [PartialOrder E] [Gendered E] (e : PersonalPronoun) (g : ℕ → E)
  (n : ℕ) (c : SpeechAct.Context PUnit E P T)

/-- A pronoun denotes the value of its index under the assignment, by the same variable lookup
for the bound, anaphoric and deictic uses. -/
theorem eq_assignment_of_mem {x : E} (h : x ∈ e.denote n c g ⟨⟩) : x = g n :=
  (PersonalPronoun.mem_denote e n c |>.1 h).2.symm

/-- A feminine pronoun denotes nothing at a referent gendered masculine. The feature does not
assert the referent's gender but presupposes it, so the pronoun has no value at all when it
fails. -/
theorem not_dom_of_masculine (hfem : e.gender = some .Fem) (h : g n ∈ Gendered.masculine) :
    ¬ (e.denote n c g ⟨⟩).Dom := by
  simp [hfem, h]

theorem she_not_dom_of_masculine (h : g n ∈ Gendered.masculine) :
    ¬ (she.denote n c g ⟨⟩).Dom :=
  not_dom_of_masculine she g n c rfl h

/-- A first-person pronoun denotes nothing at a referent that does not include the agent. -/
theorem not_dom_of_not_agent (hp : e.referentialPerson = some .first) (h : ¬ c.agent ≤ g n) :
    ¬ (e.denote n c g ⟨⟩).Dom := by
  simp [hp, h]

theorem i_not_dom_of_not_agent (h : ¬ c.agent ≤ g n) : ¬ (i.denote n c g ⟨⟩).Dom :=
  not_dom_of_not_agent i g n c (by decide) h

/-- An entry carrying only unmarked values — third person, plural, no gender — restricts the
referent to nothing, so it denotes wherever any pronoun does. Unmarked values are the absence of
a feature rather than a feature of their own, which is why the underspecified form can be used to
avoid a gender specification. -/
theorem mem_of_unmarked_features (hp : e.referentialPerson = some .third)
    (hn : e.referentialNumber = some .plural) (hg : e.gender = none) :
    g n ∈ e.denote n c g ⟨⟩ := by
  simp [hp, hn, hg]

theorem they_mem_regardless_of_gender : g n ∈ they.denote n c g ⟨⟩ :=
  mem_of_unmarked_features they g n c (by decide) (by decide) rfl

/-- The two entries come apart exactly at the referents the gender feature excludes, where *she*
has no value and *they* has one. -/
theorem they_mem_where_she_not_dom (h : g n ∈ Gendered.masculine) :
    ¬ (she.denote n c g ⟨⟩).Dom ∧ g n ∈ they.denote n c g ⟨⟩ :=
  ⟨she_not_dom_of_masculine g n c h, they_mem_regardless_of_gender g n c⟩

/-- Binding leaves the pronoun alone. The binding operator updates the assignment at the pronoun's
index, and the unchanged denotation then returns the binder. There is no bound-pronoun lexeme. -/
theorem bound_reading (b : E) {x : E} (h : x ∈ e.denote n c (Function.update g n b) ⟨⟩) :
    x = b := by
  simpa using eq_assignment_of_mem e (Function.update g n b) n c h

end Buring2012
