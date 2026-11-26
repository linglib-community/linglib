/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Pragmatics.SocialMeaning.Register
public import Linglib.Syntax.Category.Pronoun.Basic

/-!
# Personal pronouns

A personal pronoun is a pronoun with a register, the labels it agrees as and the cells of the
pronoun paradigm it is used for. Its own person, number and gender say what the form is, as a
grammar's table lists it, and by default it agrees as that and is used for that one cell. A
polite pronoun departs from the default: Italian *Lei* is a second person singular and agrees as
a third person feminine singular, and German *Sie* is a second person, used for the singular and
the plural, and agrees as a third person plural. The labels a form agrees as are its formal
features, which verbs and clitics track; its own labels and its cells are what it is used for.
The entry states all of them as labels, as a grammar does; the referents a cell covers are in
`Syntax/Category/Pronoun/Categories.lean`.

A pronoun records only features whose values are shared across languages. Honorific grades are
not: each language has its own, ordered by the deference they present, and a form may serve
several, as Maithili *tõ* is both the nonhonorific and the mid-honorific second person. A language
file
therefore states its grades as a type and its pronouns as a paradigm over them, a function from
grades to entries like the tables the grammars print. The grades a form serves are a preimage of
that function, its syncretisms the kernel, and paradigms are compared across languages by shape.

## Main definitions

* `PersonalPronoun` — a pronoun with its register, the labels it agrees as and the cells it is
  used for
* `PersonalPronoun.forms` — the forms an inventory offers for each cell, those of the pronouns
  used for a cell at least as specific
* `PersonalPronoun.ofCells`, `PersonalPronoun.ofTable`, `PersonalPronoun.ofTableAt` — the
  pronoun of a form in a table of cells, with the cases and the person and number cells of the
  cells it fills

## References

* [L. J. Adamson and S. Zompì, *Polite Pronouns and the PCC* (2025)][adamson-zompi-2025]
* [P. Kumari and P. Chandra, *Honorificity Feature as an Enabler: Bridging the Person Gap*
  (2026)][kumari-chandra-2026]
-/

@[expose] public section

/-- A personal pronoun is a `Pronoun` with its register, the labels it agrees as and the cells of
the pronoun paradigm it is used for. -/
@[ext]
structure PersonalPronoun extends Pronoun where
  /-- The register. Japanese *boku* is an informal first person, and Korean *geu* a third person
  of written narrative. -/
  register : SocialMeaning.Register := .neutral
  /-- The person, number and gender the form agrees as, by default its own. Italian *Lei*, a
  second person singular, agrees as a third person feminine singular, and K'iche' *alaq*, a
  second person plural, as a third person singular ([adamson-zompi-2025]). -/
  agreement : Agreement.Bundle := toPronoun.cell
  /-- The cells of the pronoun paradigm the form is used for, by default the cell of its own
  person, clusivity, number and gender. German *Sie* is used for the second person singular
  and plural. -/
  cells : Finset Agreement.Bundle := {toPronoun.cell}

instance : DecidableEq PersonalPronoun := fun _ _ ↦ decidable_of_iff _ PersonalPronoun.ext_iff.symm

namespace PersonalPronoun

/-! ### The forms of an inventory -/

section Forms

variable {I : Finset PersonalPronoun} {c : Agreement.Bundle} {f : String}

/-- The forms an inventory offers for a cell: those of the pronouns used for a cell at least as
specific, so that a third person singular masculine form is a form for the third person
singular. A cell no pronoun is used for gets `∅`. -/
def forms (I : Finset PersonalPronoun) (c : Agreement.Bundle) : Finset String :=
  (I.filter fun p ↦ ∃ b ∈ p.cells, c ≤ b).image (·.form)

theorem mem_forms : f ∈ forms I c ↔ ∃ p ∈ I, (∃ b ∈ p.cells, c ≤ b) ∧ p.form = f := by
  simp [forms, and_assoc]

end Forms

/-! ### The pronouns of a table -/

section Table

variable {C : Type*} (person : C → Person) (clusivity : C → Option Clusivity)
  (number : C → Option Number) (gender : C → Option UD.Gender) (case : C → Option Case)

/-- The personal pronoun `f` filling the cells `s` (`Pronoun.ofCells`), used for the person,
clusivity, number and gender of each. -/
def ofCells (s : Finset C) (f : String) : PersonalPronoun :=
  { toPronoun := .ofCells person clusivity number gender case s f,
    cells := s.image fun c ↦ .ofFeatures (.of (person := some (person c))
      (clusivity := clusivity c) (number := number c) (gender := gender c)) }

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

/-- A personal pronoun's token bears the labels the pronoun agrees as, with its case, and is of
UD pronoun type `Prs`. -/
def toWord (p : PersonalPronoun) : Morphology.Word :=
  { form := p.form, cat := .PRON,
    features := .of (person := p.agreement.person) (clusivity := p.agreement.clusivity)
      (number := p.agreement .number) (gender := p.agreement .gender) (case := p.case)
      (pronType := some .Prs) }


end PersonalPronoun
