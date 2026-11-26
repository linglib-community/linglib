/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Data.Option.NAry
public import Mathlib.Order.Nat
public import Linglib.Core.Order.Flat.Finset
public import Linglib.Data.UD.UPOS
public import Linglib.Data.UD.Features
public import Linglib.Morphology.Inflection.Paradigm.Morphome
public import Linglib.Morphology.Word.Agree
public import Linglib.Syntax.Feature.Case.Basic
public import Linglib.Syntax.Feature.Number.Basic
public import Linglib.Syntax.Feature.Person.Defs

/-!
# Pronouns

This file defines the pronoun as a lexical object: a surface form with the person, number,
gender and cases every pronoun kind shares. The kinds extend it, each in its own file: the
personal, logophoric, reflexive, reciprocal and demonstrative pronouns, and the proforms with
their interrogative and indefinite kinds. A pronoun has no denotation or pronoun type of its
own; the kind supplies them, and the token of a pronoun takes the pronoun type and the reflexive
marking as arguments. Its person, clusivity and number are labels: the referential categories
they cover are in `Syntax/Category/Pronoun/Categories.lean`, and the binding class of the token
in `Syntax/Binding/Pronoun.lean`.

## Main definitions

* `Pronoun.Strength`: the clitic, weak and strong classes of Cardinaletti and Starke, a
  bounded linear order by structural deficiency.
* `Pronoun`: the form, person, number, cases and gender of a pronoun, with its script form
  and the strength class of its series.
* `Pronoun.case`: the flat case of a pronoun, the meet of the cases it fills.
* `Pronoun.cell`: the paradigm cell that a pronoun's person, clusivity, number and gender
  name.
* `Pronoun.ofTable table f`: the pronoun of the form `f`, filling every cell the table gives it.
* `Pronoun.toWord p`: the pronoun as a token, with the pronoun type and reflexive marking of
  its kind.
* `Pronoun.agreement p`: the agreement bundle of the token.

## References

* [A. Cardinaletti and M. Starke, *The Typology of Structural Deficiency: A Case Study of the
  Three Classes of Pronouns* (1999)][cardinaletti-starke-1999]
* [H. Jung and K. Migdalski, *Toward a four-way pronoun hierarchy: A view from Slavic*
  (2022)][jung-migdalski-2022]
-/

@[expose] public section

/-! ### Structural deficiency -/

/-- The three pronoun classes of [cardinaletti-starke-1999], ordered by structural deficiency
with the most deficient least. The classes are distributional: stress does not define them. -/
inductive Pronoun.Strength where
  /-- A clitic is a deficient head, adjacent to the verb, clustering and prosodically dependent,
  as Italian *lo* and French *le*. -/
  | clitic
  /-- A weak pronoun is a deficient phrase, confined to derived positions and not coordinable,
  yet a prosodic word, as German *es* and Italian dative *loro*. -/
  | weak
  /-- A non-deficient phrase: coordinable, modifiable and free to stand in peripheral
  positions, as Italian and French *lui*. -/
  | strong
  deriving DecidableEq, Repr

namespace Pronoun.Strength

/-- The rank of a class in the deficiency order. -/
def toNat : Strength → ℕ
  | .clitic => 0
  | .weak => 1
  | .strong => 2

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> simp_all [toNat]

instance : LinearOrder Strength := LinearOrder.lift' toNat toNat_injective

instance : BoundedOrder Strength where
  bot := .clitic
  bot_le s := by cases s <;> decide
  top := .strong
  le_top s := by cases s <;> decide

end Pronoun.Strength

/-! ### The pronoun -/

/-- A pronoun is a surface form with agreement features, the core every pronoun kind shares. -/
@[ext]
structure Pronoun where
  /-- The surface form, romanized or orthographic. -/
  form : String
  /-- The grammatical person. -/
  person : Option Person := none
  /-- The clusivity of a form that marks it: Tagalog *tayo* is inclusive and *kami* exclusive,
  English *we* neither. -/
  clusivity : Option Clusivity := none
  /-- The grammatical number. -/
  number : Option Number := none
  /-- The cases the form fills: one for most forms, several for a syncretic one such as English
  *you*, none where they are unrecorded. -/
  cases : Finset Case := ∅
  /-- The grammatical gender, `none` where the form marks none. -/
  gender : Option UD.Gender := none
  /-- The form in its native script. -/
  script : Option String := none
  /-- The strength class of the series the form belongs to, `none` where it is unrecorded or
  the series has no stable class ([jung-migdalski-2022]). -/
  strength : Option Pronoun.Strength := none

instance : DecidableEq Pronoun := fun _ _ ↦ decidable_of_iff _ Pronoun.ext_iff.symm

namespace Pronoun

variable (p : Pronoun)

/-- The flat case of a pronoun: the meet of the cases it fills, `⊥` for a syncretic form and for
one whose cases are unrecorded. -/
def case : Flat Case := Flat.finsetInf p.cases (↑)

/-- The paradigm cell that the pronoun's person, clusivity, number and gender name: the
agreement bundle bearing them and nothing else. -/
def cell : Agreement.Bundle :=
  .ofFeatures (.of (person := p.person) (clusivity := p.clusivity) (number := p.number)
    (gender := p.gender))

/-! ### The pronouns of a table -/

section Table

variable {C : Type*} (person : C → Person) (clusivity : C → Option Clusivity)
  (number : C → Option Number) (gender : C → Option UD.Gender) (case : C → Option Case)

/-- The numbers of the cells `s`, a cell with no number contributing none. -/
def cellNumbers (s : Finset C) : Finset Number := s.biUnion fun c ↦ (number c).toFinset

/-- The pronoun `f` filling the cells `s`, where a cell has a person and may have a clusivity, a
number, a gender and a case: the cases of the cells, the flat value of their person, clusivity
and gender, and the number of the cells where they have one, `general` where they have several,
the form then being noncommittal between them. -/
def ofCells (s : Finset C) (f : String) : Pronoun :=
  { form := f,
    person := Flat.finsetInf s fun c ↦ (person c : Flat Person),
    clusivity := Flat.finsetInf s fun c ↦ (clusivity c : Flat Clusivity),
    number := (Flat.finsetInf (cellNumbers number s) (↑) : Option Number).or
      (if (cellNumbers number s).Nonempty then some .general else none),
    cases := s.biUnion fun c ↦ (case c).toFinset,
    gender := Flat.finsetInf s fun c ↦ (gender c : Flat UD.Gender) }

/-- The pronoun `f` of a table, filling every cell the table gives it. -/
def ofTable [Fintype C] (table : C → Finset String) (f : String) : Pronoun :=
  ofCells person clusivity number gender case (Morphology.formCellsOf table f) f

end Table

/-! ### The pronoun as a token -/

/-- The token of a pronoun is a word with its agreement features, and with the pronoun type,
reflexive marking and word class its kind supplies: a `PRON` unless the kind says otherwise, as
for a pro-adverb. -/
def toWord (pronType : Option UD.PronType := none) (reflex : Option Unit := none)
    (cat : UD.UPOS := .PRON) : Morphology.Word :=
  { form := p.form, cat := cat,
    features := .of (person := p.person) (clusivity := p.clusivity) (number := p.number)
      (gender := p.gender)
      (case := p.case) (reflex := reflex) (pronType := pronType) }

/-- The agreement bundle of a pronoun, that of its token: its person and clusivity, number,
gender and case. -/
def agreement : Agreement.Bundle := p.toWord.agreement

/-- The token of a pronoun bears the pronoun's agreement bundle, whatever its pronoun type,
reflexive marking and word class. -/
@[simp] theorem agreement_toWord (pronType : Option UD.PronType) (reflex : Option Unit)
    (cat : UD.UPOS) : (p.toWord pronType reflex cat).agreement = p.agreement :=
  rfl


end Pronoun
