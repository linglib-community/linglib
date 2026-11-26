/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Inflection.Paradigm.Basic
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reflexive
public import Linglib.Syntax.Feature.Person.Configuration

/-!
# The referential categories of a pronoun

A pronoun bears a person, a clusivity and a number as labels, and a personal pronoun names the
cells of the person and number paradigm it is used for. This file reads the labels as the
referents they cover: the referential categories of Cysouw whose referents lie in the region of
the person, narrowed by the clusivity, and have the number. English *we*, a first person plural
with no clusivity, has the three groups that contain the speaker, and Tagalog *tayo*, a first
person inclusive plural, the speaker and the addressee with others. A cell with no person or no
number has no category.

The referential categories of a personal pronoun are those of the cells it is used for. Italian
*Lei* is a second person singular and agrees as a third person feminine singular, so it denotes
the addressee: the labels it agrees as govern agreement, clitic allomorphy and reflexive binding,
and its referential categories the person-case constraint and resolved agreement.

## Main definitions

* `Agreement.Bundle.categories`: the referential categories a cell covers.
* `Pronoun.categories`: the referential categories a pronoun's own person, clusivity and number
  cover.
* `PersonalPronoun.referential`: the referential categories a personal pronoun can denote.
* `PersonalPronoun.referentialPerson`, `PersonalPronoun.referentialNumber`: the person and
  number the pronoun contributes to interpretation.
* `PersonalPronoun.IsOrdinary`: the pronoun denotes what the labels it agrees as cover.
* `PersonalPronoun.paradigm`: the forms an inventory offers for each referential category,
  whose kernel `Setoid.ker` is the inventory's person-number syncretism.
* `ReflexivePronoun.paradigm`: the forms an inventory of reflexives offers for each category
  its person and number cover.

## References

* [L. J. Adamson and S. Zompì, *Polite Pronouns and the PCC* (2025)][adamson-zompi-2025]
* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
-/

@[expose] public section

/-- The referential categories of [cysouw-2003] that a cell covers, those its person, clusivity
and number cover: none when the person or the number is unspecified, several for a syncretism
such as the first person plural with no clusivity. -/
def Agreement.Bundle.categories (b : Agreement.Bundle) : Finset Person.Category :=
  (Option.map₂ (Person.Category.ofPersonNumber · b.clusivity ·) b.person (b .number)).getD ∅

namespace Pronoun

/-- The referential categories that the pronoun's own person, clusivity and number cover. -/
def categories (p : Pronoun) : Finset Person.Category :=
  (Option.map₂ (Person.Category.ofPersonNumber · p.clusivity ·) p.person p.number).getD ∅

end Pronoun

namespace PersonalPronoun

variable {p : PersonalPronoun}

/-- The referential categories a personal pronoun can denote, those of the cells it is used
for. Italian *Lei* denotes the addressee and German *Sie* the addressee alone or with others
([adamson-zompi-2025]). -/
def referential (p : PersonalPronoun) : Finset Person.Category :=
  p.cells.biUnion Agreement.Bundle.categories

/-- The person a pronoun contributes to interpretation: the one its referential categories
share. -/
def referentialPerson (p : PersonalPronoun) : Option Person :=
  Person.Category.sharedPerson p.referential

/-- The clusivity a pronoun contributes to interpretation: the one its referential categories
share. -/
def referentialClusivity (p : PersonalPronoun) : Option Clusivity :=
  Person.Category.sharedClusivity p.referential

/-- The number a pronoun contributes to interpretation: the one its referential categories
share, `general` for a number-neutral form such as polite *Sie*. -/
def referentialNumber (p : PersonalPronoun) : Option Number :=
  Person.Category.sharedNumber p.referential

/-- An ordinary pronoun denotes exactly the categories that the labels it agrees as cover. -/
def IsOrdinary (p : PersonalPronoun) : Prop := p.referential = p.agreement.categories

instance : Decidable p.IsOrdinary := inferInstanceAs (Decidable (_ = _))

/-! ### The paradigm of an inventory -/

section Paradigm

variable {I J : Finset PersonalPronoun} {c : Person.Category} {f : String}

/-- The paradigm of an inventory assigns each referential category the forms the inventory offers
for it. A category no pronoun denotes gets `∅`, and two categories receive the same forms
exactly when the inventory does not distinguish them. -/
def paradigm : Finset PersonalPronoun → Person.Category → Finset String :=
  Morphology.formsAt (·.referential) (·.form)

theorem mem_paradigm : f ∈ paradigm I c ↔ ∃ p ∈ I, c ∈ p.referential ∧ p.form = f :=
  Morphology.mem_formsAt

@[gcongr]
theorem paradigm_mono (h : I ⊆ J) (c : Person.Category) : paradigm I c ⊆ paradigm J c :=
  Morphology.formsAt_mono h c

end Paradigm

end PersonalPronoun

namespace ReflexivePronoun

/-- The paradigm of an inventory assigns each category the forms of the reflexives whose person
and number cover it: the cells of a reflexive are those of its own labels. -/
def paradigm : Finset ReflexivePronoun → Person.Category → Finset String :=
  Morphology.formsAt (·.categories) (·.form)

theorem mem_paradigm {I : Finset ReflexivePronoun} {c : Person.Category} {f : String} :
    f ∈ paradigm I c ↔ ∃ p ∈ I, c ∈ p.categories ∧ p.form = f :=
  Morphology.mem_formsAt

end ReflexivePronoun
