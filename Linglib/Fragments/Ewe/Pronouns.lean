module

public import Linglib.Syntax.Category.Pronoun.Logophoric

/-!
# Ewe pronouns

The personal pronouns of Ewe come in three series, as Ameka tabulates them: the preverbal forms,
cliticised to the verb as its subject; the prenominal and independent forms, used before the
focus marker, before a nominal in apposition and in a possessive construction; and the postverbal
forms, the objects of verbs and prepositions. Each series has a form for three persons in two
numbers, with no clusivity and no gender. *wò* is the second person singular of the independent
and postverbal series and a third person singular subject.

The logophoric pronoun *yè*, plural *yewó*, occurs in the scope of an attitude predicate such as
'say' or 'believe' and refers to the bearer of the attitude, as Pearson describes. Ameka gives it
for the second or third person whose speech, thought or feeling a dependent clause reports, never
for the first. Sells, after Clements, gives it also under psychological predicates.

## Main definitions

* `Ewe.Pronouns.table`: the forms of each person and number in each series.
* `Ewe.Pronouns.entry`, `Ewe.Pronouns.personal`: the pronoun of a form in a person and number,
  and the inventory.
* `Ewe.Pronouns.ye`, `Ewe.Pronouns.yewó`: the logophoric pronouns.

## Main results

* `Ewe.Pronouns.paradigm_preverbal`: the subject paradigm of the inventory is the preverbal
  series.
* `Ewe.Pronouns.referential_ye`, `Ewe.Pronouns.referential_yewó`: a logophoric pronoun denotes
  the addressee or a third party, alone or with others.

## Implementation notes

* The prenominal and independent series share a row of the table, which prints two lines of
  forms for the third person without assigning them to the two. They are one series here.
* A form the table prints with optional material in parentheses is two forms, *mí(é)* being
  *mí* and *míé*. The hyphens of the bound forms are not recorded.
* A pronoun is a form in one person and number, so *wò* is two pronouns.
* The singular logophoric pronoun has the low tone mark Pearson and Sells write, *yè*. The table
  prints it without one, as it prints the plural *yewó*.

## References

* [ameka-1991]
* [pearson-2015]
* [sells-1987]
-/

@[expose] public section

namespace Ewe.Pronouns

open Person (Category)

/-- The rows of the table: a person and number each. -/
inductive Row where
  | sg1 | pl1 | sg2 | pl2 | sg3 | pl3
  deriving DecidableEq, Fintype, Repr

/-- The person of a row. -/
def Row.person : Row → Person
  | .sg1 | .pl1 => .first
  | .sg2 | .pl2 => .second
  | .sg3 | .pl3 => .third

/-- The number of a row. -/
def Row.number : Row → Number
  | .sg1 | .sg2 | .sg3 => .singular
  | .pl1 | .pl2 | .pl3 => .plural

/-- The referential categories of a row. -/
def Row.categories (r : Row) : Finset Category := Category.ofPersonNumber r.person none r.number

/-- The series of the personal pronouns. -/
inductive Series where
  /-- The preverbal forms, cliticised to the verb as its subject. -/
  | preverbal
  /-- The prenominal and independent forms, used before the focus marker, in apposition and in a
  possessive construction. -/
  | independent
  /-- The postverbal forms, the objects of verbs and prepositions. -/
  | postverbal
  deriving DecidableEq, Fintype, Repr

/-- The case a series realizes: the subject series the nominative and the object series the
accusative, the independent series none. -/
def Series.case : Series → Option Case
  | .preverbal => some .nom
  | .independent => none
  | .postverbal => some .acc

/-- The forms of each person and number in each series ([ameka-1991], Table 3.1). -/
def table : Row × Series → Finset String
  | (.sg1, .preverbal) => {"me"}
  | (.pl1, .preverbal) => {"mí", "míé"}
  | (.sg2, .preverbal) => {"è", "nè"}
  | (.pl2, .preverbal) => {"mi", "mie"}
  | (.sg3, .preverbal) => {"wò", "é"}
  | (.pl3, .preverbal) => {"wó"}
  | (.sg1, .independent) => {"nye"}
  | (.pl1, .independent) => {"miá", "miáwó"}
  | (.sg2, .independent) => {"wò"}
  | (.pl2, .independent) => {"mia", "miawó"}
  | (.sg3, .independent) => {"é", "eya"}
  | (.pl3, .independent) => {"wó", "woá", "woáwó"}
  | (.sg1, .postverbal) => {"m"}
  | (.pl1, .postverbal) => {"mí"}
  | (.sg2, .postverbal) => {"wò"}
  | (.pl2, .postverbal) => {"mi"}
  | (.sg3, .postverbal) => {"í"}
  | (.pl3, .postverbal) => {"wó"}

/-- The pronoun `f` of the row `r`, with the cases of the series it fills there. -/
def entry (r : Row) (f : String) : PersonalPronoun :=
  .ofCells (·.1.person) (some ·.1.number) (fun _ ↦ none) (·.2.case)
    ((Morphology.formCellsOf table f).filter (·.1 = r)) f

/-- The personal pronoun inventory: the entry of every form of every row. -/
def personal : Finset PersonalPronoun :=
  Finset.univ.biUnion fun r ↦ (Finset.univ.biUnion fun s ↦ table (r, s)).image (entry r)

/-- *me*, the first person singular subject. -/
def me : PersonalPronoun := entry .sg1 "me"

/-- *nye*, the first person singular independent form. -/
def nye : PersonalPronoun := entry .sg1 "nye"

/-- *m*, the first person singular object. -/
def m : PersonalPronoun := entry .sg1 "m"

/-- *mí*, the first person plural subject and object. -/
def mí : PersonalPronoun := entry .pl1 "mí"

/-- *míé*, the longer first person plural subject. -/
def míé : PersonalPronoun := entry .pl1 "míé"

/-- *miá*, the first person plural independent form. -/
def miá : PersonalPronoun := entry .pl1 "miá"

/-- *miáwó*, the longer first person plural independent form. -/
def miáwó : PersonalPronoun := entry .pl1 "miáwó"

/-- *è*, the second person singular subject. -/
def è : PersonalPronoun := entry .sg2 "è"

/-- *nè*, the longer second person singular subject. -/
def nè : PersonalPronoun := entry .sg2 "nè"

/-- *wò*, the second person singular independent form and object. -/
def wò_sg2 : PersonalPronoun := entry .sg2 "wò"

/-- *mi*, the second person plural subject and object. -/
def mi : PersonalPronoun := entry .pl2 "mi"

/-- *mie*, the longer second person plural subject. -/
def mie : PersonalPronoun := entry .pl2 "mie"

/-- *mia*, the second person plural independent form. -/
def mia : PersonalPronoun := entry .pl2 "mia"

/-- *miawó*, the longer second person plural independent form. -/
def miawó : PersonalPronoun := entry .pl2 "miawó"

/-- *wò*, a third person singular subject. -/
def wò_sg3 : PersonalPronoun := entry .sg3 "wò"

/-- *é*, a third person singular subject and independent form. -/
def é : PersonalPronoun := entry .sg3 "é"

/-- *eya*, a third person singular independent form. -/
def eya : PersonalPronoun := entry .sg3 "eya"

/-- *í*, the third person singular object. -/
def í : PersonalPronoun := entry .sg3 "í"

/-- *wó*, the third person plural of every series. -/
def wó : PersonalPronoun := entry .pl3 "wó"

/-- *woá*, a third person plural independent form. -/
def woá : PersonalPronoun := entry .pl3 "woá"

/-- *woáwó*, the longer form of *woá*. -/
def woáwó : PersonalPronoun := entry .pl3 "woáwó"

/-- A form of a row denotes the row's categories. -/
theorem referential_entry :
    ∀ r s, ∀ f ∈ table (r, s), (entry r f).referential = r.categories := by
  decide +kernel

/-- The subject paradigm of the inventory is the preverbal series. -/
theorem paradigm_preverbal :
    ∀ r, ∀ c ∈ r.categories,
      PersonalPronoun.paradigm (personal.filter (.nom ∈ ·.cases)) c = table (r, .preverbal) := by
  decide +kernel

/-- *wò* is one form and two pronouns, a second person and a third. -/
theorem wò_sg2_ne_wò_sg3 : wò_sg2.form = wò_sg3.form ∧ wò_sg2.person ≠ wò_sg3.person := by
  decide +kernel

/-! ### The logophoric pronouns -/

/-- The logophoric form of each row, none in the first person ([ameka-1991], Table 3.1). -/
def logophoricForms : Row → Finset String
  | .sg1 | .pl1 => ∅
  | .sg2 | .sg3 => {"yè"}
  | .pl2 | .pl3 => {"yewó"}

/-- The logophoric pronoun `f`, with the rows it fills. -/
def logophoricOf (f : String) : LogophoricPronoun :=
  ⟨.ofTable Row.person (some ·.number) (fun _ ↦ none) (fun _ ↦ none) logophoricForms f⟩

/-- The logophoric pronoun *yè*. -/
def ye : LogophoricPronoun := logophoricOf "yè"

/-- The plural logophoric pronoun *yewó*. -/
def yewó : LogophoricPronoun := logophoricOf "yewó"

/-- A row has a logophoric form exactly when it is not first person. -/
theorem logophoricForms_nonempty_iff (r : Row) :
    (logophoricForms r).Nonempty ↔ r.person ≠ .first := by
  cases r <;> decide

/-- *yè* denotes the addressee or a third party. -/
theorem referential_ye : ye.referential = {.addressee, .other} := by decide +kernel

/-- *yewó* denotes the addressee or a third party with others. -/
theorem referential_yewó : yewó.referential = {.addresseeOthers, .others} := by decide +kernel

end Ewe.Pronouns
