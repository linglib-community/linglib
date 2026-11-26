/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Inflection.Paradigm.Basic
public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Syntax.Category.Pronoun.Basic
public import Linglib.Syntax.Binding.Word

/-!
# Personal pronouns

A personal pronoun is a pronoun with a register and the cells of the person and number paradigm
it is used for. The cells are by default the one its own person, clusivity and number name. A
polite pronoun overrides the default: Italian *Lei* agrees as a third person singular and is used
for the second person singular, and German *Sie* agrees as a third person plural and is used for
the second person of either number. The entry states both as labels, as a grammar does; the
referents a cell covers are in `Syntax/Category/Pronoun/Categories.lean`.

A pronoun records only features whose values are shared across languages. Honorific grades are
not: each language has its own, ordered by the deference they present, and a form may serve
several, as Maithili *tõ* is both the nonhonorific and the mid-honorific second person. A language
file
therefore states its grades as a type and its pronouns as a paradigm over them, a function from
grades to entries like the tables the grammars print. The grades a form serves are a preimage of
that function, its syncretisms the kernel, and paradigms are compared across languages by shape.

## Main definitions

* `PersonalPronoun` — a pronoun with its register and the cells it is used for
* `PersonalPronoun.forms` — the forms an inventory offers for each cell, whose kernel
  `Setoid.ker` is the inventory's syncretism
* `PersonalPronoun.ofCells`, `PersonalPronoun.ofTable`, `PersonalPronoun.ofTableAt` — the
  pronoun of a form in a table of cells, with the cases and the person and number cells of the
  cells it fills

## Main results

* `PersonalPronoun.bindingClassOf_toWord` — a personal pronoun is a pronominal

## References

* [L. J. Adamson and S. Zompì, *Polite Pronouns and the PCC* (2025)][adamson-zompi-2025]
* [P. Kumari and P. Chandra, *Honorificity Feature as an Enabler: Bridging the Person Gap*
  (2026)][kumari-chandra-2026]
-/

@[expose] public section

/-- A personal pronoun is a `Pronoun` with its register and the cells of the person and number
paradigm it is used for. -/
@[ext]
structure PersonalPronoun extends Pronoun where
  /-- The register. Japanese *boku* is an informal first person, and Korean *geu* a third person
  of written narrative. -/
  register : SocialMeaning.Register := .neutral
  /-- The cells of the person and number paradigm the form is used for, by default the cell of
  its own person, clusivity and number. Italian *Lei* is used for the second person singular
  and German *Sie* for the second person singular and plural ([adamson-zompi-2025]). -/
  cells : Finset Agreement.Bundle := {toPronoun.cell}

instance : DecidableEq PersonalPronoun := fun _ _ ↦ decidable_of_iff _ PersonalPronoun.ext_iff.symm

namespace PersonalPronoun

/-! ### The forms of an inventory -/

section Forms

variable {I : Finset PersonalPronoun} {c : Agreement.Bundle} {f : String}

/-- The forms an inventory offers for each cell of the person and number paradigm. A cell no
pronoun is used for gets `∅`, and two cells receive the same forms exactly when the inventory
does not distinguish them. -/
def forms : Finset PersonalPronoun → Agreement.Bundle → Finset String :=
  Morphology.formsAt (·.cells) (·.form)

theorem mem_forms : f ∈ forms I c ↔ ∃ p ∈ I, c ∈ p.cells ∧ p.form = f :=
  Morphology.mem_formsAt

end Forms

/-! ### The pronouns of a table -/

section Table

variable {C : Type*} (person : C → Person) (clusivity : C → Option Clusivity)
  (number : C → Option Number) (gender : C → Option UD.Gender) (case : C → Option Case)

/-- The personal pronoun `f` filling the cells `s` (`Pronoun.ofCells`), used for the person,
clusivity and number of each. -/
def ofCells (s : Finset C) (f : String) : PersonalPronoun :=
  { toPronoun := .ofCells person clusivity number gender case s f,
    cells := s.image fun c ↦ .ofFeatures
      (.of (person := some (person c)) (clusivity := clusivity c) (number := number c)) }

/-- The personal pronoun `f` of a table, filling every cell the table gives it. -/
def ofTable [Fintype C] (table : C → Finset String) (f : String) : PersonalPronoun :=
  ofCells person clusivity number gender case (Morphology.formCellsOf table f) f

/-- The personal pronoun `f` at the value `k` of `key` in a table, filling the cells with that
value that the table gives it. With the row as key this is the form of one row, for a table in
which one form serves rows that are different pronouns. -/
def ofTableAt [Fintype C] {κ : Type*} [DecidableEq κ] (key : C → κ) (k : κ)
    (table : C → Finset String) (f : String) : PersonalPronoun :=
  ofCells person clusivity number gender case
    ((Morphology.formCellsOf table f).filter (key · = k)) f

end Table

/-! ### The pronoun as a token -/

/-- A personal pronoun's token is of UD pronoun type `Prs`. -/
def toWord (p : PersonalPronoun) : Morphology.Word := p.toPronoun.toWord (some .Prs)

/-- A personal pronoun is a pronominal. -/
@[simp]
theorem bindingClassOf_toWord (p : PersonalPronoun) :
    Binding.bindingClassOf p.toWord = some .pronoun :=
  p.toPronoun.bindingClassOf_toWord (by decide) (by decide)

end PersonalPronoun
