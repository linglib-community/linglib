module

public import Linglib.Morphology.Morph
public import Linglib.Morphology.Paradigm.Contiguity
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Maithili pronouns

The nominative and accusative personal pronouns of the Darbhanga variety of Maithili, with the
suffix that agrees with a second person subject. The second person has four honorific grades and
the third person two. The nonhonorific and the mid-honorific second person share *tõ* and *tora*,
which the verb tells apart, while the high honorific *əpne* takes the agreement of the honorific
*əhã*. The two third-person grades share the nominative *o* and differ in the accusative.

## Main results

* `Maithili.Pronouns.second_nom_eq_iff`: the second-person pronouns separate every pair of grades
  except the nonhonorific and the mid-honorific.
* `Maithili.Pronouns.secondAgreement_eq_iff`: the verb separates every pair except the honorific
  and the high honorific.

## References

* [P. Kumari and P. Chandra, *Honorificity Feature as an Enabler: Bridging the Person Gap*
  (2026)][kumari-chandra-2026]
-/

@[expose] public section

namespace Maithili

/-- The honorific grades of Maithili, lowest first, with the addressees [kumari-chandra-2026] gives
for each (pp. 120–121 and fns. 9–10). -/
inductive Grade where
  /-- The nonhonorific grade, to a younger sibling. -/
  | nonhonorific
  /-- The mid-honorific grade, to a younger relative once grown up or a younger stranger. -/
  | midHonorific
  /-- The honorific grade, to parents, teachers and anyone older. -/
  | honorific
  /-- The high honorific grade, to someone addressed formally, such as a high official. -/
  | highHonorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

/-- The cases of the Maithili pronoun table, the nominative and the accusative. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative. -/
  | acc
  deriving DecidableEq, Fintype, Repr

namespace Pronouns

open Morphology

/-- *həm*, 1sg nominative. -/
def ham : PersonalPronoun := { form := "həm", person := some .first, number := some .singular }

/-- *həmra*, 1sg accusative. -/
def hamra : PersonalPronoun := { form := "həmra", person := some .first, number := some .singular }

/-- *tõ*, 2sg nominative. -/
def toN : PersonalPronoun := { form := "tõ", person := some .second, number := some .singular }

/-- *tora*, 2sg accusative. -/
def tora : PersonalPronoun := { form := "tora", person := some .second, number := some .singular }

/-- *əhã*, 2sg nominative. -/
def ahaN : PersonalPronoun := { form := "əhã", person := some .second, number := some .singular }

/-- *əhãke*, 2sg accusative. -/
def ahaNke : PersonalPronoun :=
  { form := "əhãke", person := some .second, number := some .singular }

/-- *əpne*, 2sg nominative. -/
def apne : PersonalPronoun := { form := "əpne", person := some .second, number := some .singular }

/-- *o*, 3sg nominative. -/
def o : PersonalPronoun := { form := "o", person := some .third, number := some .singular }

/-- *okra*, 3sg accusative. -/
def okra : PersonalPronoun := { form := "okra", person := some .third, number := some .singular }

/-- *hunka*, 3sg accusative. -/
def hunka : PersonalPronoun := { form := "hunka", person := some .third, number := some .singular }

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {ham, hamra, toN, tora, ahaN, ahaNke, apne, o, okra, hunka}

/-- The second person by case and grade, [kumari-chandra-2026]'s Table 3 with the nominative
*əpne* of fn. 10, whose accusative the source does not give. -/
def second : Case → Grade → Option PersonalPronoun
  | .nom, .nonhonorific => some toN
  | .nom, .midHonorific => some toN
  | .nom, .honorific => some ahaN
  | .nom, .highHonorific => some apne
  | .acc, .nonhonorific => some tora
  | .acc, .midHonorific => some tora
  | .acc, .honorific => some ahaNke
  | .acc, .highHonorific => none

/-- The third person by case and grade, [kumari-chandra-2026]'s Table 3, which gives it only the
nonhonorific and the honorific grade. -/
def third : Case → Grade → Option PersonalPronoun
  | .nom, .nonhonorific => some o
  | .nom, .honorific => some o
  | .acc, .nonhonorific => some okra
  | .acc, .honorific => some hunka
  | _, _ => none

/-- Two second-person grades share their nominative exactly when both are below the honorific. -/
theorem second_nom_eq_iff (g h : Grade) :
    second .nom g = second .nom h ↔ g = h ∨ g < .honorific ∧ h < .honorific := by
  revert g h; decide

theorem isContiguous_second_nom : IsContiguous (second .nom) := by
  unfold IsContiguous; decide

theorem third_nom_eq_acc_ne :
    third .nom .nonhonorific = third .nom .honorific ∧
      third .acc .nonhonorific ≠ third .acc .honorific := by
  decide

/-- The suffix agreeing with a second person subject at each grade, in the past tense of an
intransitive verb ([kumari-chandra-2026] (18) and fn. 10). -/
def secondAgreement : Grade → Morph
  | .nonhonorific => .suff "æ"
  | .midHonorific => .suff "əh"
  | .honorific => .suff "əũh"
  | .highHonorific => .suff "əũh"

/-- The verb separates every pair of second-person grades except the honorific and the high
honorific, the two the pronouns separate as *əhã* and *əpne*. -/
theorem secondAgreement_eq_iff (g h : Grade) :
    secondAgreement g = secondAgreement h ↔ g = h ∨ .midHonorific < g ∧ .midHonorific < h := by
  revert g h; decide

end Pronouns

end Maithili
