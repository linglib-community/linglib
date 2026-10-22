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
*lo*, *la*, *li* and *le*, dative *gli* and *le* in the singular and *loro* or *gli* in the plural,
and reflexive *si*, which marks neither gender nor number. The atonic forms are clitics except the
third-person plural dative *loro*, which Cardinaletti and Starke class as weak: it is deficient,
but it follows the verb, never enters a cluster and bears word stress.

## Main declarations

* `Italian.Pronouns.pronouns` — the tonic series
* `Italian.Pronouns.atonic` — the atonic object pronouns by person, number, gender and case
* `Italian.Pronouns.accusative`, `Italian.Pronouns.dative`, `Italian.Pronouns.reflexiveForms`,
  `Italian.Pronouns.reflexive` — the atonic series
* `Italian.Pronouns.atonic_acc_eq_atonic_dat_iff`, `Italian.Pronouns.atonic_eq_reflexiveForms_iff` —
  the atonic series differ in the third person alone
* `Italian.Pronouns.strength_eq_weak_iff` — dative *loro* is the one atonic form that is not a
  clitic

## Implementation notes

An atonic pronoun is a form with the cells it fills, so *mi* is one clitic with the accusative and
the dative of the first person singular, as Table 6.A gives it. A form whose cells are not all the
combinations of their categories and cases is split: *le* is a singular dative and a plural
accusative, and two entries (`formCellsOf_atonic_le`). The variants *me*, *te*, *glie*, *ce* and
*ve* that clitics take before another clitic (§6.2) are not recorded.

## References

* [L. J. Adamson and S. Zompì, *Polite Pronouns and the PCC* (2025)][adamson-zompi-2025]
* [M. Maiden and C. Robustelli, *A Reference Grammar of Modern Italian*
  (2007)][maiden-robustelli-2007]
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

/-! ### The atonic series -/

/-- The rows of the atonic pronouns: a person and number each, and in the third person a gender. -/
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

/-- The cases of the atonic pronouns. -/
inductive Case where
  /-- The accusative, the direct object. -/
  | acc
  /-- The dative, the indirect object. -/
  | dat
  deriving DecidableEq, Fintype, Repr

/-- The comparative value of a case. -/
def Case.label : Case → _root_.Case
  | acc => .acc
  | dat => .dat

/-- The atonic pronouns of each cell ([maiden-robustelli-2007] Tables 6.A and 6.B, pp. 95–96).
The third person plural dative is formal *loro* or everyday *gli* (§6.7, p. 102). -/
def atonic : Row × Case → Finset String
  | (.sg1, _) => {"mi"}
  | (.sg2, _) => {"ti"}
  | (.sg3m, .acc) => {"lo"}
  | (.sg3f, .acc) => {"la"}
  | (.sg3m, .dat) => {"gli"}
  | (.sg3f, .dat) => {"le"}
  | (.pl1, _) => {"ci"}
  | (.pl2, _) => {"vi"}
  | (.pl3m, .acc) => {"li"}
  | (.pl3f, .acc) => {"le"}
  | (.pl3m, .dat) | (.pl3f, .dat) => {"loro", "gli"}

/-- The clitic `f` filling the cells `s`. -/
def cliticOf (s : Finset (Row × Case)) (f : String) : PersonalPronoun :=
  { PersonalPronoun.ofCells (·.1.person) (some ·.1.number) (·.1.gender) (some ·.2.label) s f with
    strength := some .clitic }

/-- The clitic `f`, filling every cell the table gives it. -/
def clitic (f : String) : PersonalPronoun := cliticOf (Morphology.formCellsOf atonic f) f

/-- *mi*, first person singular. -/
def mi : PersonalPronoun := clitic "mi"

/-- *ti*, second person singular. -/
def ti : PersonalPronoun := clitic "ti"

/-- *ci*, first person plural. -/
def ci : PersonalPronoun := clitic "ci"

/-- *vi*, second person plural. -/
def vi : PersonalPronoun := clitic "vi"

/-- *lo*, third person singular masculine accusative. -/
def lo : PersonalPronoun := clitic "lo"

/-- *la*, third person singular feminine accusative. -/
def la : PersonalPronoun := clitic "la"

/-- *li*, third person plural masculine accusative. -/
def li : PersonalPronoun := clitic "li"

/-- *gli*, third person singular masculine dative and third person plural dative. -/
def gli : PersonalPronoun := clitic "gli"

/-- *le*, third person singular feminine dative. -/
def le_dat : PersonalPronoun := cliticOf {(.sg3f, .dat)} "le"

/-- *le*, third person plural feminine accusative. -/
def le_acc : PersonalPronoun := cliticOf {(.pl3f, .acc)} "le"

/-- *loro*, third person plural dative, a weak pronoun that follows the verb. -/
def loro_dat : PersonalPronoun := { clitic "loro" with strength := some .weak }

/-- The accusative series. -/
def accusative : Finset PersonalPronoun := {mi, ti, lo, la, ci, vi, li, le_acc}

/-- The dative series. -/
def dative : Finset PersonalPronoun := {mi, ti, gli, le_dat, ci, vi, loro_dat}

/-- *le* fills the third person singular feminine dative and the third person plural feminine
accusative, cells that differ in number and in case, so it is two entries: one entry with both
cases and both numbers would also claim the singular accusative and the plural dative. -/
theorem formCellsOf_atonic_le :
    Morphology.formCellsOf atonic "le" = {(.sg3f, .dat), (.pl3f, .acc)} := by
  decide

/-- The series give each case the forms of its column of the table. -/
theorem forms_accusative_dative :
    accusative.image (·.form) = Finset.univ.biUnion (fun r ↦ atonic (r, .acc)) ∧
      dative.image (·.form) = Finset.univ.biUnion (fun r ↦ atonic (r, .dat)) := by
  decide

/-! ### The reflexive series -/

/-- The reflexive forms of each row: the first and second person forms "also function as reflexive
pronouns", and the third person has *si* (Tables 6.A and 6.B, p. 96). -/
def reflexiveForms : Row → Finset String
  | .sg1 => {"mi"}
  | .sg2 => {"ti"}
  | .pl1 => {"ci"}
  | .pl2 => {"vi"}
  | _ => {"si"}

/-- The reflexive clitic `f`, with the rows it fills. -/
def reflexiveOf (f : String) : ReflexivePronoun :=
  ⟨{ Pronoun.ofTable Row.person (some ·.number) Row.gender (fun _ ↦ none) reflexiveForms f with
      strength := some .clitic }⟩

/-- *mi*, first person singular reflexive. -/
def mi_refl : ReflexivePronoun := reflexiveOf "mi"

/-- *ti*, second person singular reflexive. -/
def ti_refl : ReflexivePronoun := reflexiveOf "ti"

/-- *si*, third person reflexive of either number. -/
def si : ReflexivePronoun := reflexiveOf "si"

/-- *ci*, first person plural reflexive. -/
def ci_refl : ReflexivePronoun := reflexiveOf "ci"

/-- *vi*, second person plural reflexive. -/
def vi_refl : ReflexivePronoun := reflexiveOf "vi"

/-- The reflexive series. -/
def reflexive : Finset ReflexivePronoun := (Finset.univ.biUnion reflexiveForms).image reflexiveOf

/-! ### Syncretism and strength -/

/-- The accusative and the dative of a row are the same exactly outside the third person
(Tables 6.A and 6.B). -/
theorem atonic_acc_eq_atonic_dat_iff (r : Row) :
    atonic (r, .acc) = atonic (r, .dat) ↔ r.person ≠ .third := by
  cases r <;> decide

/-- The atonic forms of a row are its reflexive exactly outside the third person, where the
reflexive *si* "does not distinguish case, gender or number" (p. 96). -/
theorem atonic_eq_reflexiveForms_iff (r : Row) (k : Case) :
    atonic (r, k) = reflexiveForms r ↔ r.person ≠ .third := by
  cases r <;> cases k <;> decide

/-- Dative *loro* is the one atonic object form that is weak rather than a clitic. -/
theorem strength_eq_weak_iff {p : PersonalPronoun} (hp : p ∈ accusative ∪ dative) :
    p.strength = some .weak ↔ p = loro_dat := by
  revert p; decide +kernel

end Pronouns

end Italian
