module

public import Linglib.Syntax.Category.Pronoun.Personal
public import Linglib.Syntax.Category.Pronoun.Reciprocal
public import Linglib.Syntax.Category.Pronoun.Reflexive
public import Linglib.Fragments.German.Case

/-!
# German pronouns

This file defines the German personal pronouns, the reflexive *sich* and the reciprocal
*einander*, and the case paradigms of the interrogative pronouns *wer* 'who' and *was* 'what',
which also head free relatives.

The second person distinguishes the familiar *du* and *ihr* from the polite level, with the
single form *Sie*. *Sie* takes the third person plural series for agreement and reflexive
binding (*sich*, not *dich* or *euch*) while denoting the addressee alone or with others, so its
`person` is third and its `referential` categories are those of *du* and *ihr* together. *wer*
declines for the four German cases; *was* has one form for the nominative and the accusative and
no dative.

## Main definitions

* `German.Pronouns.pronouns` — the personal pronoun inventory
* `German.Pronouns.addresseeSg`, `German.Pronouns.addresseePl` — the pronouns of address at each
  grade
* `German.Pronouns.sich`, `German.Pronouns.einander` — the reflexive and the reciprocal pronoun
* `German.Pronouns.wer`, `German.Pronouns.was` — the interrogative paradigms, a form for each case

## Main results

* `German.Pronouns.addresseeSg_eq_sie_formal_iff`, `German.Pronouns.addressee_number`,
  `German.Pronouns.sie_formal_referential` — *Sie* is the pronoun of the polite grade, which does
  not distinguish one addressee from several, and it denotes what the two familiar forms denote
  together
* `German.Pronouns.wer_nonempty`, `German.Pronouns.was_nonempty_iff` — *wer* has a form in every
  case, *was* in every case but the dative

## References

* [L. J. Adamson and S. Zompì, *Polite pronouns and the PCC* (2025)][adamson-zompi-2025]
* [M. Dalrymple and R. M. Kaplan, *Feature indeterminacy and feature resolution*
  (2000)][dalrymple-kaplan-2000]
* [N. Evans, *Reciprocal Constructions: Towards a Structural Typology* (2008)][evans-2008]
* [V. Gast and F. Haas, *On Reciprocal and Reflexive Uses of Anaphors in German and Other European
  Languages* (2008)][gast-haas-2008]
-/

@[expose] public section

namespace German

/-- The honorific grades of German pronouns, lowest first. -/
inductive Grade where
  /-- The familiar grade, *du* and *ihr*. -/
  | familiar
  /-- The polite grade, *Sie*. -/
  | polite
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

namespace Pronouns

/-! ### Personal pronouns -/

/-- The first person singular *ich*. -/
def ich : PersonalPronoun := { form := "ich", person := some .first, number := some .singular }

/-- The familiar second person singular *du*. -/
def du : PersonalPronoun := { form := "du", person := some .second, number := some .singular }

/-- The polite second person *Sie*, for one or several addressees. Its agreement person and
number are those of the third person plural; it denotes the addressee alone or with others
([adamson-zompi-2025]). -/
def sie_formal : PersonalPronoun :=
  { form := "Sie", person := some .third, number := some .plural,
    referential := {.addressee, .addresseeOthers} }

/-- The third person singular masculine *er*. -/
def er : PersonalPronoun :=
  { form := "er", person := some .third, number := some .singular, gender := some .masculine }

/-- The third person singular feminine *sie*. -/
def sie_sg : PersonalPronoun :=
  { form := "sie", person := some .third, number := some .singular, gender := some .feminine }

/-- The third person singular neuter *es*. -/
def es : PersonalPronoun :=
  { form := "es", person := some .third, number := some .singular, gender := some .neuter }

/-- The first person plural *wir*. -/
def wir : PersonalPronoun := { form := "wir", person := some .first, number := some .plural }

/-- The familiar second person plural *ihr*. -/
def ihr : PersonalPronoun := { form := "ihr", person := some .second, number := some .plural }

/-- The third person plural *sie*. -/
def sie_pl : PersonalPronoun := { form := "sie", person := some .third, number := some .plural }

/-- The pronoun for a single addressee at each grade. -/
def addresseeSg : Grade → PersonalPronoun
  | .familiar => du
  | .polite => sie_formal

/-- The pronoun for several addressees at each grade. -/
def addresseePl : Grade → PersonalPronoun
  | .familiar => ihr
  | .polite => sie_formal

/-- The personal pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {ich, du, sie_formal, er, sie_sg, es, wir, ihr, sie_pl}

/-- *Sie* is the pronoun of the polite grade and of no other, for one addressee or several. -/
theorem addresseeSg_eq_sie_formal_iff (g : Grade) :
    (addresseeSg g = sie_formal ↔ g = .polite) ∧ (addresseePl g = sie_formal ↔ g = .polite) := by
  cases g <;> decide

/-- The familiar grade distinguishes one addressee from several, and the polite grade does not. -/
theorem addressee_number :
    addresseeSg .familiar ≠ addresseePl .familiar ∧ addresseeSg .polite = addresseePl .polite := by
  decide

/-- The polite form denotes exactly what the two familiar forms denote between them: *Sie* is
number-neutral where the familiar level distinguishes *du* from *ihr*. -/
theorem sie_formal_referential : sie_formal.referential = du.referential ∪ ihr.referential := by
  decide

/-! ### Reflexive and reciprocal pronouns -/

/-- The third person reflexive *sich*, one form for both numbers and for the accusative and the
dative; the first and second persons use their personal forms as reflexives. This is the
pronominal *sich* of [gast-haas-2008], a noun phrase that is only reflexive; the clitic *sich* of
reciprocal and middle verbs is a marker in `German.Reciprocals`. -/
def sich : ReflexivePronoun := { form := "sich", person := some .third }

/-- The reciprocal *einander* 'each other', invariant for person, number and case. It fuses *ein*
'one' and *ander* 'other' ([gast-haas-2008]) into a single word that also compounds with a
preposition (*an-einander*, *miteinander*), the kind of fused bipartite form that [evans-2008]
classes with the reciprocal pronouns (p. 48). -/
def einander : ReciprocalPronoun := { form := "einander" }

/-! ### Interrogative pronouns

The animate *wer* declines for the four German cases; the inanimate *was* has one form for the
nominative and the accusative and no dative. Each paradigm gives each case its finset of forms, so
`Morphology.formCellsOf` reads the cases a form realizes straight off it. -/

/-- The paradigm of *wer* 'who'. -/
def wer : Case → Finset String
  | .nom => {"wer"}
  | .acc => {"wen"}
  | .dat => {"wem"}
  | .gen => {"wessen"}

/-- The paradigm of *was* 'what'. -/
def was : Case → Finset String
  | .nom | .acc => {"was"}
  | .gen => {"wessen"}
  | .dat => ∅

/-- *wer* has a form for every case. -/
theorem wer_nonempty (c : Case) : (wer c).Nonempty := by
  cases c <;> decide

/-- *was* has a form for every case but the dative. -/
theorem was_nonempty_iff (c : Case) : (was c).Nonempty ↔ c ≠ .dat := by
  cases c <;> decide

end Pronouns

end German
