module

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

* `Spanish.Clitics.accusative`, `Spanish.Clitics.dative` — the two object series, personal
  pronouns of the clitic strength class
* `Spanish.Clitics.reflexive` — the reflexive series
* `Spanish.Clitics.paradigm_accusative_eq_paradigm_dative_iff`,
  `Spanish.Clitics.paradigm_dative_eq_paradigm_reflexive_iff` — the series are syncretic exactly
  outside the third person
* `Spanish.Clitics.isSome_gender_iff` — gender is marked by the third-person accusatives alone

## References

* [J. Butt, C. Benjamin and A. Moreira Rodríguez, *A New Reference Grammar of Modern Spanish*
  (2019)][butt-benjamin-2019]
-/

@[expose] public section

namespace Spanish.Clitics

/-! ### The accusative series -/

/-- *me*, first person singular accusative. -/
def me_acc : PersonalPronoun :=
  { form := "me", person := some .first, number := some .singular, cases := {.acc},
    strength := some .clitic }

/-- *te*, second person singular accusative. -/
def te_acc : PersonalPronoun :=
  { form := "te", person := some .second, number := some .singular, cases := {.acc},
    strength := some .clitic }

/-- *lo*, third person singular masculine accusative. -/
def lo : PersonalPronoun :=
  { form := "lo", person := some .third, number := some .singular, cases := {.acc},
    gender := some .masculine, strength := some .clitic }

/-- *la*, third person singular feminine accusative. -/
def la : PersonalPronoun :=
  { form := "la", person := some .third, number := some .singular, cases := {.acc},
    gender := some .feminine, strength := some .clitic }

/-- *nos*, first person plural accusative. -/
def nos_acc : PersonalPronoun :=
  { form := "nos", person := some .first, number := some .plural, cases := {.acc},
    strength := some .clitic }

/-- *os*, second person plural accusative, used in Spain. -/
def os_acc : PersonalPronoun :=
  { form := "os", person := some .second, number := some .plural, cases := {.acc},
    strength := some .clitic }

/-- *los*, third person plural masculine accusative. -/
def los : PersonalPronoun :=
  { form := "los", person := some .third, number := some .plural, cases := {.acc},
    gender := some .masculine, strength := some .clitic }

/-- *las*, third person plural feminine accusative. -/
def las : PersonalPronoun :=
  { form := "las", person := some .third, number := some .plural, cases := {.acc},
    gender := some .feminine, strength := some .clitic }

/-- The accusative series. -/
def accusative : Finset PersonalPronoun := {me_acc, te_acc, lo, la, nos_acc, os_acc, los, las}

/-! ### The dative series -/

/-- *me*, first person singular dative. -/
def me_dat : PersonalPronoun :=
  { form := "me", person := some .first, number := some .singular, cases := {.dat},
    strength := some .clitic }

/-- *te*, second person singular dative. -/
def te_dat : PersonalPronoun :=
  { form := "te", person := some .second, number := some .singular, cases := {.dat},
    strength := some .clitic }

/-- *le*, third person singular dative. -/
def le : PersonalPronoun :=
  { form := "le", person := some .third, number := some .singular, cases := {.dat},
    strength := some .clitic }

/-- *nos*, first person plural dative. -/
def nos_dat : PersonalPronoun :=
  { form := "nos", person := some .first, number := some .plural, cases := {.dat},
    strength := some .clitic }

/-- *os*, second person plural dative, used in Spain. -/
def os_dat : PersonalPronoun :=
  { form := "os", person := some .second, number := some .plural, cases := {.dat},
    strength := some .clitic }

/-- *les*, third person plural dative. -/
def les : PersonalPronoun :=
  { form := "les", person := some .third, number := some .plural, cases := {.dat},
    strength := some .clitic }

/-- *se*, the form *le* and *les* take before a third-person accusative clitic, as in
*se lo doy* 'I give it to them'. It is number-neutral. -/
def se_dat : PersonalPronoun :=
  { form := "se", person := some .third, number := some .general, cases := {.dat},
    strength := some .clitic }

/-- The dative series. -/
def dative : Finset PersonalPronoun := {me_dat, te_dat, le, nos_dat, os_dat, les, se_dat}

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

/-- The accusative and the dative have the same forms exactly outside the third person. -/
theorem paradigm_accusative_eq_paradigm_dative_iff (c : Person.Category) :
    PersonalPronoun.paradigm accusative c = PersonalPronoun.paradigm dative c ↔
      c.person ≠ .third := by
  cases c <;> decide +kernel

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
