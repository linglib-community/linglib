module

public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reflexive

/-!
# Italian pronouns

Italian has a tonic series of personal pronouns and an atonic series of object pronouns. The
tonic second person distinguishes familiar *tu* and *voi* from polite *Lei*, which agrees as a
third person singular, and the archaic polite plural *Loro*.

The atonic first and second persons have one form each for direct object, indirect object and
reflexive use: *mi*, *ti*, *ci* and *vi*. Only the third person tells the three apart: accusative
*lo*, *la*, *li* and *le*, dative *gli* and *le*, and reflexive *si*, which marks neither gender
nor number. The atonic forms are clitics except the third-person plural dative *loro*, which
Cardinaletti and Starke class as weak: it is deficient, but it follows the verb, never enters a
cluster and bears word stress.

## Main declarations

* `Italian.Pronouns.pronouns` — the tonic series
* `Italian.Pronouns.accusative`, `Italian.Pronouns.dative`, `Italian.Pronouns.reflexive` — the
  atonic series
* `Italian.Pronouns.paradigm_accusative_eq_paradigm_dative_iff`,
  `Italian.Pronouns.paradigm_dative_eq_paradigm_reflexive_iff` — the atonic series are syncretic
  exactly outside the third person
* `Italian.Pronouns.strength_eq_weak_iff` — dative *loro* is the one atonic form that is not a
  clitic

## References

* [L. J. Adamson and S. Zompì, *Polite Pronouns and the PCC* (2025)][adamson-zompi-2025]
* [A. Cardinaletti and M. Starke, *The Typology of Structural Deficiency: A Case Study of the
  Three Classes of Pronouns* (1999)][cardinaletti-starke-1999]
-/

@[expose] public section

namespace Italian

/-- The honorific grades of Italian pronouns, lowest first. -/
inductive Grade where
  /-- The familiar grade, *tu* and *voi*. -/
  | familiar
  /-- The polite grade, *Lei* and *Loro*. -/
  | polite
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-! ### The tonic series -/

/-- *io* — 1sg. -/
def io : PersonalPronoun :=
  { form := "io", person := some .first, number := some .singular, strength := some .strong }

/-- *tu* — 2sg familiar (T form). -/
def tu : PersonalPronoun :=
  { form := "tu", person := some .second, number := some .singular,
    strength := some .strong }

/-- The polite second person singular *Lei*, the V form. It agrees as a third person singular,
patterns with the feminine singular clitics and binds the third-person reflexive *si*, but it
denotes the addressee, so it triggers PCC and Fancy Constraint effects and second person plural
resolved agreement in coordination ([adamson-zompi-2025]). -/
def lei_formal : PersonalPronoun :=
  { form := "Lei", person := some .third, number := some .singular,
    referential := {.addressee}, strength := some .strong }

/-- *lui* — 3sg masculine. -/
def lui : PersonalPronoun :=
  { form := "lui", person := some .third, number := some .singular, gender := some .masculine,
    strength := some .strong }

/-- *lei* — 3sg feminine. -/
def lei : PersonalPronoun :=
  { form := "lei", person := some .third, number := some .singular, gender := some .feminine,
    strength := some .strong }

/-- *noi* — 1pl. -/
def noi : PersonalPronoun :=
  { form := "noi", person := some .first, number := some .plural, strength := some .strong }

/-- *voi* — 2pl (familiar; also used as general 2pl in modern Italian). -/
def voi : PersonalPronoun :=
  { form := "voi", person := some .second, number := some .plural,
    strength := some .strong }

/-- *Loro* — 2pl formal (archaic, largely replaced by *voi*). -/
def loro_formal : PersonalPronoun :=
  { form := "Loro", person := some .second, number := some .plural,
    strength := some .strong }

/-- *loro* — 3pl. -/
def loro : PersonalPronoun :=
  { form := "loro", person := some .third, number := some .plural, strength := some .strong }

/-- The second person singular at each grade. -/
def addresseeSg : Grade → PersonalPronoun
  | .familiar => tu
  | .polite => lei_formal

/-- The second person plural at each grade. -/
def addresseePl : Grade → PersonalPronoun
  | .familiar => voi
  | .polite => loro_formal

/-- The strong-pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {io, tu, lei_formal, lui, lei, noi, voi, loro_formal, loro}

/-! ### The accusative series -/

/-- *mi*, first person singular accusative. -/
def mi_acc : PersonalPronoun :=
  { form := "mi", person := some .first, number := some .singular, cases := {.acc},
    strength := some .clitic }

/-- *ti*, second person singular accusative. -/
def ti_acc : PersonalPronoun :=
  { form := "ti", person := some .second, number := some .singular, cases := {.acc},
    strength := some .clitic }

/-- *lo*, third person singular masculine accusative. -/
def lo : PersonalPronoun :=
  { form := "lo", person := some .third, number := some .singular, cases := {.acc},
    gender := some .masculine, strength := some .clitic }

/-- *la*, third person singular feminine accusative. -/
def la : PersonalPronoun :=
  { form := "la", person := some .third, number := some .singular, cases := {.acc},
    gender := some .feminine, strength := some .clitic }

/-- *ci*, first person plural accusative. -/
def ci_acc : PersonalPronoun :=
  { form := "ci", person := some .first, number := some .plural, cases := {.acc},
    strength := some .clitic }

/-- *vi*, second person plural accusative. -/
def vi_acc : PersonalPronoun :=
  { form := "vi", person := some .second, number := some .plural, cases := {.acc},
    strength := some .clitic }

/-- *li*, third person plural masculine accusative. -/
def li : PersonalPronoun :=
  { form := "li", person := some .third, number := some .plural, cases := {.acc},
    gender := some .masculine, strength := some .clitic }

/-- *le*, third person plural feminine accusative. -/
def le_acc : PersonalPronoun :=
  { form := "le", person := some .third, number := some .plural, cases := {.acc},
    gender := some .feminine, strength := some .clitic }

/-- The accusative series. -/
def accusative : Finset PersonalPronoun :=
  {mi_acc, ti_acc, lo, la, ci_acc, vi_acc, li, le_acc}

/-! ### The dative series -/

/-- *mi*, first person singular dative. -/
def mi_dat : PersonalPronoun :=
  { form := "mi", person := some .first, number := some .singular, cases := {.dat},
    strength := some .clitic }

/-- *ti*, second person singular dative. -/
def ti_dat : PersonalPronoun :=
  { form := "ti", person := some .second, number := some .singular, cases := {.dat},
    strength := some .clitic }

/-- *gli*, third person singular masculine dative. -/
def gli : PersonalPronoun :=
  { form := "gli", person := some .third, number := some .singular, cases := {.dat},
    gender := some .masculine, strength := some .clitic }

/-- *le*, third person singular feminine dative. -/
def le_dat : PersonalPronoun :=
  { form := "le", person := some .third, number := some .singular, cases := {.dat},
    gender := some .feminine, strength := some .clitic }

/-- *ci*, first person plural dative. -/
def ci_dat : PersonalPronoun :=
  { form := "ci", person := some .first, number := some .plural, cases := {.dat},
    strength := some .clitic }

/-- *vi*, second person plural dative. -/
def vi_dat : PersonalPronoun :=
  { form := "vi", person := some .second, number := some .plural, cases := {.dat},
    strength := some .clitic }

/-- *loro*, third person plural dative, a weak pronoun that follows the verb. -/
def loro_dat : PersonalPronoun :=
  { form := "loro", person := some .third, number := some .plural, cases := {.dat},
    strength := some .weak }

/-- The dative series. -/
def dative : Finset PersonalPronoun :=
  {mi_dat, ti_dat, gli, le_dat, ci_dat, vi_dat, loro_dat}

/-! ### The reflexive series -/

/-- *mi*, first person singular reflexive. -/
def mi_refl : ReflexivePronoun :=
  { form := "mi", person := some .first, number := some .singular, strength := some .clitic }

/-- *ti*, second person singular reflexive. -/
def ti_refl : ReflexivePronoun :=
  { form := "ti", person := some .second, number := some .singular, strength := some .clitic }

/-- *si*, third person reflexive, number-neutral. -/
def si : ReflexivePronoun :=
  { form := "si", person := some .third, number := some .general, strength := some .clitic }

/-- *ci*, first person plural reflexive. -/
def ci_refl : ReflexivePronoun :=
  { form := "ci", person := some .first, number := some .plural, strength := some .clitic }

/-- *vi*, second person plural reflexive. -/
def vi_refl : ReflexivePronoun :=
  { form := "vi", person := some .second, number := some .plural, strength := some .clitic }

/-- The reflexive series. -/
def reflexive : Finset ReflexivePronoun := {mi_refl, ti_refl, si, ci_refl, vi_refl}

/-! ### Syncretism and strength -/

/-- The accusative and the dative have the same forms exactly outside the third person. -/
theorem paradigm_accusative_eq_paradigm_dative_iff (c : Person.Category) :
    PersonalPronoun.paradigm accusative c = PersonalPronoun.paradigm dative c ↔
      c.person ≠ .third := by
  cases c <;> decide +kernel

/-- The dative and the reflexive have the same forms exactly outside the third person. -/
theorem paradigm_dative_eq_paradigm_reflexive_iff (c : Person.Category) :
    PersonalPronoun.paradigm dative c = ReflexivePronoun.paradigm reflexive c ↔
      c.person ≠ .third := by
  cases c <;> decide +kernel

/-- Dative *loro* is the one atonic object form that is weak rather than a clitic. -/
theorem strength_eq_weak_iff {p : PersonalPronoun} (hp : p ∈ accusative ∪ dative) :
    p.strength = some .weak ↔ p = loro_dat := by
  revert p; decide +kernel

end Pronouns

end Italian
