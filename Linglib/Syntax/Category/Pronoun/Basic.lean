module

public import Mathlib.Data.Option.NAry
public import Mathlib.Order.Nat
public import Linglib.Core.Order.Flat.Finset
public import Linglib.Data.UD.UPOS
public import Linglib.Data.UD.Features
public import Linglib.Morphology.Paradigm.Morphome
public import Linglib.Morphology.Word.Agree
public import Linglib.Syntax.Agreement.Phi
public import Linglib.Syntax.Binding.Basic
public import Linglib.Syntax.Case.Basic
public import Linglib.Syntax.Gender.Basic
public import Linglib.Syntax.Person.Category

/-!
# Pronouns

This file defines the pronoun as a lexical object: a surface form with the agreement features
every pronoun kind shares. The kinds extend it, each in its own file: `PersonalPronoun`,
`LogophoricPronoun`, `ReflexivePronoun`, `ReciprocalPronoun`, `DemonstrativePronoun`,
`InterrogativePronoun` and `IndefinitePronoun`. A `Pronoun` has no denotation, pronoun type or
binding class of its own; the kind supplies them, and `Pronoun.toWord` takes the last two as
arguments.

## Main definitions

* `Pronoun.Strength`: the clitic, weak and strong classes of Cardinaletti and Starke, a
  bounded linear order by structural deficiency.
* `Pronoun`: the form, person, number, cases and gender of a pronoun, with its script form
  and the strength class of its series.
* `Pronoun.case`: the flat case of a pronoun, the meet of the cases it fills.
* `Pronoun.ofCells`, `Pronoun.ofTable`: the pronoun of a form in a table of cells.
* `Pronoun.categories`: the referential categories of Cysouw that the person and number
  realize.
* `Pronoun.WellFormed`: clusivity is not borne by a singular.
* `Pronoun.toWord`: the pronoun as a token, with the pronoun type and reflexive marking of
  its kind; `Pronoun.phi_toWord` says the token bears the pronoun's φ-features.
* `Pronoun.CandidateAntecedent`: a nominal token that agrees with the pronoun, so one of the
  pronoun's number (`Pronoun.CandidateAntecedent.number_eq`).

## Main results

* `Pronoun.bindingClassOf_toWord_reflex`, `Pronoun.bindingClassOf_toWord_rcp`,
  `Pronoun.bindingClassOf_toWord`: the binding class the engine reads off a pronoun's token is
  fixed by the marking its kind supplies.

## References

* [L. Bloomfield, *Language* (1933)][bloomfield-1933]
* [A. Cardinaletti and M. Starke, *The Typology of Structural Deficiency: A Case Study of the
  Three Classes of Pronouns* (1999)][cardinaletti-starke-1999]
* [N. Chomsky, *Lectures on Government and Binding* (1981)][chomsky-1981]
* [M. Cysouw, *The Paradigmatic Structure of Person Marking* (2003)][cysouw-2003]
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
  /-- The grammatical person. Clusivity is a person value: Tagalog *tayo* is
  `firstInclusive` and *kami* `firstExclusive`, English *we* plain `first` ([cysouw-2003]). -/
  person : Option Person := none
  /-- The grammatical number. -/
  number : Option Number := none
  /-- The cases the form fills: one for most forms, several for a syncretic one such as English
  *you*, none where they are unrecorded. -/
  cases : Finset Case := ∅
  /-- The grammatical gender, `none` where the form marks none. -/
  gender : Option Gender.Label := none
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

/-- The referential categories of [cysouw-2003] that the person and number realize: none when
either is unspecified, several for a syncretism such as clusivity-unmarked English *we*. -/
def categories : Finset Person.Category :=
  (Option.map₂ Person.Category.ofPersonNumber p.person p.number).getD ∅

/-- A pronoun bears the bundle of its person, number, gender and case. -/
def phi : Agreement.Bundle
  | .person => p.person
  | .number => p.number
  | .gender => p.gender
  | .case => p.case
  | .definiteness => ⊥

instance : HasPhi Pronoun := ⟨phi⟩

/-- Clusivity is not borne by a singular: the inclusive and exclusive persons split the first
person non-singular ([cysouw-2003]). -/
def WellFormed : Prop :=
  ∀ per ∈ p.person, per.MarksClusivity → p.number ≠ some .singular

instance : Decidable p.WellFormed :=
  inferInstanceAs (Decidable (∀ per ∈ p.person, _ → _))

/-! ### The pronouns of a table -/

section Table

variable {C : Type*} (person : C → Person) (number : C → Option Number)
  (gender : C → Option Gender.Label) (case : C → Option Case)

/-- The categories of the cells `s`, those each cell's person and number realize. -/
def cellCategories (s : Finset C) : Finset Person.Category :=
  s.biUnion fun c ↦ ((number c).map (Person.Category.ofPersonNumber (person c))).getD ∅

/-- The pronoun `f` filling the cells `s`, where a cell has a person and may have a number, a
gender and a case: the cases of the cells, the flat value of their person and gender, and the
number their categories share, `general` for cells of both numbers. -/
def ofCells (s : Finset C) (f : String) : Pronoun :=
  { form := f,
    person := Flat.finsetInf s fun c ↦ (person c : Flat Person),
    number := Person.Category.sharedNumber (cellCategories person number s),
    cases := s.biUnion fun c ↦ (case c).toFinset,
    gender := Flat.finsetInf s fun c ↦ (gender c : Flat Gender.Label) }

/-- The pronoun `f` of a table, filling every cell the table gives it. -/
def ofTable [Fintype C] (table : C → Finset String) (f : String) : Pronoun :=
  ofCells person number gender case (Morphology.formCellsOf table f) f

end Table

/-! ### The pronoun as a token -/

/-- The token of a pronoun is a `PRON` word with its agreement features, and with the pronoun
type and reflexive marking its kind supplies. -/
def toWord (pronType : Option UD.PronType := none) (reflex : Option Unit := none) :
    Morphology.Word :=
  { form := p.form, cat := .PRON,
    features := .of (person := p.person) (number := p.number) (gender := p.gender)
      (case_ := p.case) (reflex := reflex) (pronType := pronType) }

/-- The token of a pronoun bears the pronoun's φ-features, whatever its pronoun type and reflexive
marking. -/
@[simp] theorem phi_toWord (pronType : Option UD.PronType) (reflex : Option Unit) :
    HasPhi.phi (p.toWord pronType reflex) = HasPhi.phi p := by
  funext d; cases d <;> rfl

/-- A token marked reflexive classifies as a reflexive anaphor. -/
@[simp]
theorem bindingClassOf_toWord_reflex (t : Option UD.PronType) :
    Binding.bindingClassOf (p.toWord t (some ())) = some .reflexive := by
  simp [Binding.bindingClassOf, toWord, Morphology.Features.of]

/-- A token of reciprocal pronoun type classifies as a reciprocal anaphor. -/
@[simp]
theorem bindingClassOf_toWord_rcp :
    Binding.bindingClassOf (p.toWord (some .Rcp)) = some .reciprocal := by
  simp [Binding.bindingClassOf, toWord, Morphology.Features.of]

/-- Any other pronoun token classifies as a pronominal, the elsewhere class of
[chomsky-1981]. -/
theorem bindingClassOf_toWord {t : Option UD.PronType} (ht : t ≠ some .Rcp) :
    Binding.bindingClassOf (p.toWord t) = some .pronoun := by
  rcases t with _ | t <;> (try cases t) <;>
    simp_all +decide [Binding.bindingClassOf, toWord, Morphology.Features.of]

/-- A candidate antecedent of a pronoun is a nominal token that agrees with it: a pro-form
takes its antecedents from a fixed form-class ([bloomfield-1933]). -/
def CandidateAntecedent (w : Morphology.Word) : Prop :=
  Binding.IsNominal w.cat ∧ HasPhi.Agree p w

instance (w : Morphology.Word) : Decidable (p.CandidateAntecedent w) :=
  inferInstanceAs (Decidable (_ ∧ _))

variable {p} in
/-- A candidate antecedent has the pronoun's number, where both mark one. -/
theorem CandidateAntecedent.number_eq {w : Morphology.Word} (h : p.CandidateAntecedent w)
    {n m : Number} (hp : p.number = some n) (hw : w.features .number = some m) : n = m :=
  Flat.compat_iff.mp (h.2.apply .number) n hp m hw

end Pronoun
