module

public import Linglib.Core.Order.Flat.Finset
public import Linglib.Morphology.Paradigm.Morphome
public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# Spanish object clitics

Spanish object pronouns are clitics on the verb. The first and second persons have one form each
for direct object, indirect object and reflexive use: *me*, *te*, *nos* and *os*. Only the third
person tells the three apart: accusative *lo*, *la*, *los* and *las* mark gender and number,
dative *le* and *les* mark number alone, and reflexive *se* marks neither. A third-person dative
is replaced by *se* before a third-person accusative, *se lo doy* and never *le lo doy*, so *se*
is also a form of the dative. *Os* belongs to *vosotros* and is confined to Spain; elsewhere the
third-person plural forms serve for plural addressees. The description follows Butt, Benjamin and
Moreira Rodríguez's reference grammar.

## Main declarations

* `Spanish.Clitics.table` — the object clitics by person, number, gender and case
* `Spanish.Clitics.entry`, `Spanish.Clitics.accusative`, `Spanish.Clitics.dative` — a clitic with
  the cells its form fills, and the two object series
* `Spanish.Clitics.reflexive` — the reflexive series
* `Spanish.Clitics.table_acc_eq_table_dat_iff`,
  `Spanish.Clitics.paradigm_dative_eq_paradigm_reflexive_iff` — the series are syncretic exactly
  outside the third person
* `Spanish.Clitics.isSome_gender_iff` — gender is marked by the third-person accusatives alone

## Implementation notes

A clitic is a form with the cells it fills, as the grammar treats *me* as one object pronoun and
not as a direct and an indirect object homonym (§14.1): *me* has the accusative and the dative of
the first person singular, and a clitic cluster's position, not the entry, decides which case a
clitic bears. Dative *se* fills the third-person datives beside *le* and *les*, so its flat number
is unspecified and its referential categories are those of both numbers.

## References

* [J. Butt, C. Benjamin and A. Moreira Rodríguez, *A New Reference Grammar of Modern Spanish*
  (2019)][butt-benjamin-2019]
-/

@[expose] public section

namespace Spanish.Clitics

open Morphology

/-! ### The object clitics -/

/-- The rows of the object clitics: a person and number each, and in the third person a gender. -/
inductive Row where
  | sg1 | sg2 | sg3m | sg3f | pl1 | pl2 | pl3m | pl3f
  deriving DecidableEq, Fintype, Repr

/-- The person of a row. -/
def Row.person : Row → Person
  | .sg1 | .pl1 => .first
  | .sg2 | .pl2 => .second
  | .sg3m | .sg3f | .pl3m | .pl3f => .third

/-- The number of a row. -/
def Row.number : Row → Number
  | .sg1 | .sg2 | .sg3m | .sg3f => .singular
  | .pl1 | .pl2 | .pl3m | .pl3f => .plural

/-- The gender of a row, marked in the third person alone. -/
def Row.gender : Row → Option Gender
  | .sg3m | .pl3m => some .masculine
  | .sg3f | .pl3f => some .feminine
  | _ => none

/-- The cases of the object clitics. -/
inductive Case where
  /-- The accusative. -/
  | acc
  /-- The dative. -/
  | dat
  deriving DecidableEq, Fintype, Repr

/-- The comparative value of a case. -/
def Case.label : Case → _root_.Case
  | acc => .acc
  | dat => .dat

/-- The object clitics of each cell ([butt-benjamin-2019] §14.1, pp. 143–144). A third-person
dative also has *se*, the form it takes before a third-person accusative (§14.9.1, p. 155). -/
def table : Row × Case → Finset String
  | (.sg1, _) => {"me"}
  | (.sg2, _) => {"te"}
  | (.sg3m, .acc) => {"lo"}
  | (.sg3f, .acc) => {"la"}
  | (.sg3m, .dat) | (.sg3f, .dat) => {"le", "se"}
  | (.pl1, _) => {"nos"}
  | (.pl2, _) => {"os"}
  | (.pl3m, .acc) => {"los"}
  | (.pl3f, .acc) => {"las"}
  | (.pl3m, .dat) | (.pl3f, .dat) => {"les", "se"}

/-- The clitic `f`, with the cases and referential categories of the cells it fills and their flat
person, number and gender. -/
def entry (f : String) : PersonalPronoun :=
  { form := f,
    person := Flat.finsetInf (formCellsOf table f) fun c ↦ (c.1.person : Flat Person),
    number := Flat.finsetInf (formCellsOf table f) fun c ↦ (c.1.number : Flat Number),
    cases := (formCellsOf table f).image (·.2.label),
    gender := Flat.finsetInf (formCellsOf table f) fun c ↦ (c.1.gender : Flat Gender),
    strength := some .clitic,
    referential := (formCellsOf table f).biUnion fun c ↦
      Person.Category.ofPersonNumber c.1.person c.1.number }

/-- The clitics of a case. -/
def series (k : Case) : Finset PersonalPronoun :=
  (Finset.univ.biUnion fun r ↦ table (r, k)).image entry

/-- The accusative series. -/
def accusative : Finset PersonalPronoun := series .acc

/-- The dative series. -/
def dative : Finset PersonalPronoun := series .dat

/-- *me*, first person singular. -/
def me : PersonalPronoun := entry "me"

/-- *te*, second person singular. -/
def te : PersonalPronoun := entry "te"

/-- *nos*, first person plural. -/
def nos : PersonalPronoun := entry "nos"

/-- *os*, second person plural, used in Spain. -/
def os : PersonalPronoun := entry "os"

/-- *lo*, third person singular masculine accusative. -/
def lo : PersonalPronoun := entry "lo"

/-- *la*, third person singular feminine accusative. -/
def la : PersonalPronoun := entry "la"

/-- *los*, third person plural masculine accusative. -/
def los : PersonalPronoun := entry "los"

/-- *las*, third person plural feminine accusative. -/
def las : PersonalPronoun := entry "las"

/-- *le*, third person singular dative. -/
def le : PersonalPronoun := entry "le"

/-- *les*, third person plural dative. -/
def les : PersonalPronoun := entry "les"

/-- *se*, the third-person dative before a third-person accusative clitic, as in *se lo doy* 'I
give it to them'. -/
def se_dat : PersonalPronoun := entry "se"

/-! ### The reflexive series -/

/-- *me*, first person singular reflexive. -/
def me_refl : ReflexivePronoun :=
  { form := "me", person := some .first, number := some .singular, strength := some .clitic }

/-- *te*, second person singular reflexive. -/
def te_refl : ReflexivePronoun :=
  { form := "te", person := some .second, number := some .singular, strength := some .clitic }

/-- *se*, third person reflexive, number-neutral. -/
def se : ReflexivePronoun :=
  { form := "se", person := some .third, number := some .general, strength := some .clitic }

/-- *nos*, first person plural reflexive. -/
def nos_refl : ReflexivePronoun :=
  { form := "nos", person := some .first, number := some .plural, strength := some .clitic }

/-- *os*, second person plural reflexive, used in Spain. -/
def os_refl : ReflexivePronoun :=
  { form := "os", person := some .second, number := some .plural, strength := some .clitic }

/-- The reflexive series. -/
def reflexive : Finset ReflexivePronoun := {me_refl, te_refl, se, nos_refl, os_refl}

/-! ### Syncretism across the series -/

/-- "Only the third-person set has two forms" (§14.1, p. 143): the accusative and the dative of
a row are the same exactly outside the third person. -/
theorem table_acc_eq_table_dat_iff (r : Row) :
    table (r, .acc) = table (r, .dat) ↔ r.person ≠ .third := by
  cases r <;> decide

/-- The dative and the reflexive have the same forms exactly outside the third person, where the
dative has *le* or *les* beside *se* and the reflexive *se* alone. -/
theorem paradigm_dative_eq_paradigm_reflexive_iff (c : Person.Category) :
    PersonalPronoun.paradigm dative c = ReflexivePronoun.paradigm reflexive c ↔
      c.person ≠ .third := by
  cases c <;> decide +kernel

/-- Every category has a reflexive form. -/
theorem paradigm_reflexive_nonempty (c : Person.Category) :
    (ReflexivePronoun.paradigm reflexive c).Nonempty := by
  cases c <;> decide +kernel

/-- Gender is marked by the third-person accusatives alone. -/
theorem isSome_gender_iff {p : PersonalPronoun} (hp : p ∈ accusative ∪ dative) :
    p.gender.isSome ↔ p.person = some .third ∧ .acc ∈ p.cases := by
  revert p; decide +kernel

end Spanish.Clitics
