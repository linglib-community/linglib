module

public import Linglib.Data.Examples.Karlsson2017
public import Linglib.Data.Examples.Readers
public import Linglib.Data.Wordlist.Karlsson2017
public import Linglib.Fragments.Finnish.Morphotactics
public import Linglib.Morphology.Word.UD
public import Linglib.Semantics.Negation.Polarity

/-!
# Karlsson (2017): Finnish: A Comprehensive Grammar

This file formalizes Karlsson's rules for the case of a Finnish object and his tables of endings.
The object is *partitive* if the sentence is negative, the action irresultative or the quantity
indefinite, and otherwise takes a *total-object case*: the accusative for a personal pronoun, the
nominative for a numeral or a plural, and for a singular the genitive, or the nominative under an
imperative, a passive, an obligation or an infinitival subject. [The partitive is thus the
stronger case](##Object.case_eq_part_iff). The Finnish Fragment's morphotactics derives [the
printed object of each of the grammar's examples in the case the rules assign](##rows_derived), and
[the forms of its tables](##forms_derived), from their stems.

## Implementation notes

* Resultativity is the grammar's own notion, whether the action leads to a result, and is not
  identified with telicity.
* The Fragment's phonemes do not write the *g* of *digi=kamera-n*, so one example goes unread.
* A form of the tables is read in the Finnish case whose comparative label is its cell's case.

## References

* [karlsson-2017]
-/

@[expose] public section

namespace Karlsson2017

/-- The kind of nominal serving as object, as the total-object rules of section 13.3.2 tell them
apart: a personal pronoun or *kuka* 'who' (rule 1), a numeral heading its phrase (rule 3), or any
other nominal, plural (rule 2) or singular (rule 4). -/
inductive Nominal
  | personalPronoun | numeral | other
  deriving DecidableEq, Repr

/-- The clause types, the last four being those under which a singular total object is in the
nominative (section 13.3.2, rule 4b). -/
inductive Clause
  | finite | imperative | passive | obligation | infinitival
  deriving DecidableEq, Repr

/-- Whether the action leads to an 'important' final result (section 12.2.2, rule 2a), as
*Tyttö luk-i kirja-n* 'The girl read (= completed reading) a/the book' does and *Tyttö luk-i
kirja-a* 'The girl was reading a/the book' does not. -/
inductive Resultativity
  | resultative | irresultative
  deriving DecidableEq, Repr

/-- The quantity an object expresses (section 12.2.2, rule 3): a whole or a definite quantity, or
an indefinite, non-limited quantity, as divisible and plural words express. It is not the
definiteness of the object: *Osta-n jäätelö-n* 'I('ll) buy an/the ice-cream' expresses a definite
quantity on either reading. -/
inductive Quantity
  | definite | indefinite
  deriving DecidableEq, Repr

/-- An object with the factors the grammar's rules read: the polarity of the sentence, the
resultativity of the action, the quantity the object expresses, its kind of nominal, its number
and the type of its clause. -/
structure Object where
  polarity : Polarity
  resultativity : Resultativity
  quantity : Quantity
  nominal : Nominal
  number : Finnish.Nominal.numberSystem
  clause : Clause
  deriving DecidableEq

namespace Object

/-- The partitive conditions of section 12.2.2: a negative sentence, an irresultative action and
an indefinite quantity. -/
def IsPartitive (o : Object) : Prop :=
  o.polarity = .negative ∨ o.resultativity = .irresultative ∨ o.quantity = .indefinite

instance : DecidablePred IsPartitive := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The total-object case of section 13.3.2. -/
def totalCase (o : Object) : Finnish.Case :=
  match o.nominal with
  | .personalPronoun => .acc
  | .numeral => .nom
  | .other =>
    Number.elim Finnish.Nominal.numberSystem (if o.clause = .finite then .gen else .nom) .nom
      (n := o.number)

/-- The case of the object: the partitive under any partitive condition, and otherwise the
total-object case (section 13.3.1). -/
def case (o : Object) : Finnish.Case := if o.IsPartitive then .part else o.totalCase

theorem totalCase_ne_part (o : Object) : o.totalCase ≠ .part := by
  unfold totalCase Number.elim
  split <;> (try split_ifs) <;> decide

/-- The partitive is the stronger object case: the object is partitive exactly under a partitive
condition, whatever its kind of nominal, its number and its clause (section 13.3.1). -/
theorem case_eq_part_iff (o : Object) : o.case = .part ↔ o.IsPartitive := by
  unfold case
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (totalCase_ne_part o) h

/-- A total object needs an affirmative sentence, a resultative action and a definite quantity,
all three. -/
theorem case_ne_part_iff (o : Object) :
    o.case ≠ .part ↔ o.polarity = .positive ∧ o.resultativity = .resultative ∧
      o.quantity = .definite := by
  rcases o with ⟨_ | _, _ | _, _ | _, _, _, _⟩ <;> simp [case_eq_part_iff, IsPartitive]

/-- In an affirmative sentence about a definite quantity the object is partitive exactly when the
action is irresultative: the case marks the aspect (section 12.2.2, rule 2a). -/
theorem part_iff_irresultative {o : Object} (hp : o.polarity = .positive) (hq : o.quantity = .definite) :
    o.case = .part ↔ o.resultativity = .irresultative := by
  simp [case_eq_part_iff, IsPartitive, hp, hq]

end Object

/-! ### The printed objects -/

section Objects

open Phonology

/-- The phonemes a printed word writes, without the boundaries and marks of the grammar's
segmentation (`-`, `=`, `>`, `+`), a capital as its small letter. -/
def spell (w : List Char) : Option (List Segment) :=
  ((w.filter (· ∉ ['-', '=', '>', '+'])).map Char.toLower).mapM Finnish.ofChar

/-- An example's object, its stem, the part of the printed object before the first inflectional
boundary, and its form. -/
structure Row where
  object : Object
  stem : List Segment
  form : List Segment

/-- The printed object is a surface form of its stem in the case `c`, in the object's number. -/
def Row.Realizes (r : Row) (c : Finnish.Case) : Prop :=
  r.form ∈ Finnish.Nominal.realize r.stem (Finnish.Nominal.endings r.object.number c)

instance (r : Row) (c : Finnish.Case) : Decidable (r.Realizes c) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- A row read through the grammar's terms, failing on a term it does not use. -/
def Row.ofDatum (e : Datum) : Option Row := do
  let p ← e.parse? "negated" [("yes", Polarity.negative), ("no", .positive)]
  let t ← e.parse? "aspect" [("resultative", Resultativity.resultative),
    ("irresultative", .irresultative)]
  let q ← e.parse? "quantity" [("definite", Quantity.definite), ("indefinite", .indefinite)]
  let n ← e.parse? "nominal" [("personalPronoun", Nominal.personalPronoun),
    ("numeral", .numeral), ("other", .other)]
  let num ← e.parse? "number" [("singular", ⟨.singular, by decide⟩),
    ("plural", ⟨.plural, by decide⟩)]
  let cl ← e.parse? "clause" [("finite", Clause.finite), ("imperative", .imperative),
    ("passive", .passive), ("obligation", .obligation), ("infinitival", .infinitival)]
  let w := (← e.feature? "object").toList
  some ⟨⟨p, t, q, n, num, cl⟩, ← spell (w.takeWhile (· ≠ '-')), ← spell w⟩

/-- The printed object of each example of sections 12.2.2 and 13.3 is a form, in its number, of
the case the grammar's rules assign, and a form of the partitive exactly under a partitive
condition. -/
theorem rows_derived :
    (∀ e ∈ Examples.all, ∀ r ∈ Row.ofDatum e,
      r.Realizes r.object.case ∧ (r.Realizes .part ↔ r.object.IsPartitive)) ∧
      Datum.ReadCount Row.ofDatum Examples.all 43 := by
  decide +kernel

-- Section 12.2.2, rule 2a: *Tyttö luk-i kirja-a* 'The girl was reading a/the book' is affirmative
-- and its quantity definite, but its object is no form of the genitive, against the statement
-- of the total-object conditions in section 13.3.1 (p. 212), which joins resultativity and
-- quantity by "or".
theorem exists_affirmative_definite_not_total : ∃ e ∈ Examples.all, ∃ r ∈ Row.ofDatum e,
    r.object.polarity = .positive ∧ r.object.quantity = .definite ∧
      ¬ r.Realizes r.object.totalCase := by
  decide +kernel

end Objects

/-! ### The tables of endings -/

section Tables

open Finnish Phonology CLDF.Wordlist

/-- A word of the tables is given by its stem and its endings. -/
structure Word where
  stem : List Segment
  endings : List (Σ σ, Nominal.Exponent σ)

/-- The agreement of a possessive suffix. -/
def possessorOf : Wordlist.Possessor → Agreement.Bundle
  | .sg1 => .personNumber .first .singular
  | .sg2 => .personNumber .second .singular
  | .sg3 => .personNumber .third .singular
  | .pl1 => .personNumber .first .plural
  | .pl2 => .personNumber .second .plural
  | .pl3 => .personNumber .third .plural

/-- The infinitive of the tables' label. -/
def infinitiveOf : Wordlist.Infinitive → Infinitive
  | .a => .a
  | .e => .e
  | .ma => .ma

/-- The clitic of the tables' label. -/
def cliticOf : Wordlist.Clitic → Clitic
  | .kO => .kO
  | .kin => .kin
  | .hAn => .hAn
  | .kAAn => .kAAn

/-- The number of a cell, the singular unless the cell is plural. -/
def numberOf (c : Wordlist.Cell) : Nominal.numberSystem :=
  if (c.number : Option UD.Number) = some .Plur then ⟨.plural, by decide⟩
  else ⟨.singular, by decide⟩

/-- The word of a form of the tables in the case `c`: the stem the grammar segments off, then
the function ending of its infinitive, the endings of its number and of `c`, its possessive
ending and its clitic. -/
def Word.ofForm (f : Form Wordlist.Cell) (c : Finnish.Case) : Option Word := do
  let stem ← f.morphs.head?.bind (spell ·.toList)
  let inf := (f.cell.infinitive : Option Wordlist.Infinitive).map infinitiveOf
  let p := (f.cell.possessor : Option Wordlist.Possessor).map possessorOf
  let k := (f.cell.clitic : Option Wordlist.Clitic).map cliticOf
  some ⟨stem, (inf.map (⟨_, .infinitive ·⟩)).toList ++ Nominal.endings (numberOf f.cell) c ++
    (p.map (⟨_, .possessive ·⟩)).toList ++ (k.map (⟨_, .clitic ·⟩)).toList⟩

/-- The Fragment derives each form of the tables: in the Finnish case labelled by the cell's
case, the endings of its cell make a word, and the stem with those endings has the form among
its surface forms. -/
theorem forms_derived : ∀ f ∈ Wordlist.all, ∃ c : Finnish.Case,
    (f.cell.case : Option UD.Case) = some c.label.toUD ∧ ∃ w ∈ Word.ofForm f c,
      Nominal.WellFormed w.endings ∧
        ∃ x ∈ spell f.form.toList, x ∈ Nominal.realize w.stem w.endings := by
  decide +kernel

end Tables

end Karlsson2017
