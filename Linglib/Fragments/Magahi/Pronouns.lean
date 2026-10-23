module

public import Linglib.Morphology.Morph
public import Linglib.Morphology.Paradigm.Contiguity
public import Linglib.Syntax.Category.Pronoun.Personal

/-!
# Magahi pronouns and agreement

The personal pronouns of Magahi and the verb suffixes that agree with the honorific grade of the
subject and of the addressee, as Alok tabulates them. The second and third persons have three
grades, nonhonorific, honorific and high honorific. The second person singular has one pronoun,
*tu*, for the two lower grades, and the verb tells them apart. The third person singular has one
nominative, *u*, for all three grades, and its oblique forms separate the nonhonorific from the
two higher grades. The suffix agreeing with the addressee is fused with the one agreeing with the
subject.

## Main results

* `Magahi.Pronouns.secondSingular_eq_iff`, `Magahi.Pronouns.thirdSingular_eq_iff`: the second
  person singular merges the two lower grades and the third person oblique the two higher ones.
* `Magahi.Pronouns.secondAgreement_injective`: the verb separates the grades *tu* merges.
* `Magahi.Pronouns.allocutive_honorific`: honorific and high honorific subjects take the same
  fused suffixes.

## References

* [D. Alok, *Speaker and Addressee in Natural Language: Honorificity, Indexicality and Their
  Interaction in Magahi* (2020)][alok-2020]
* [D. Alok and O. Bhalla, *Allocutivity and the Syntax of Honorifics* (2026)][alok-bhalla-2026]
-/

@[expose] public section

namespace Magahi

/-- The honorific grades of Magahi, lowest first. -/
inductive Grade where
  /-- The nonhonorific grade. -/
  | nonhonorific
  /-- The honorific grade. -/
  | honorific
  /-- The high honorific grade. -/
  | highHonorific
  deriving DecidableEq, Fintype, Repr

instance : LinearOrder Grade := LinearOrder.lift' Grade.ctorIdx (by decide)

/-- The cases of the Magahi pronoun tables, the nominative, the accusative and the possessive. -/
inductive Case where
  /-- The nominative. -/
  | nom
  /-- The accusative, also the dative. -/
  | acc
  /-- The possessive. -/
  | poss
  deriving DecidableEq, Fintype, Repr

namespace Pronouns

open Morphology

/-! ### First person -/

/-- *ham* 'I'. -/
def ham : PersonalPronoun := { form := "ham", person := some .first, number := some .singular }

/-- *hamraa* 'me'. -/
def hamraa : PersonalPronoun :=
  { form := "hamraa", person := some .first, number := some .singular }

/-- *hamar* 'my'. -/
def hamar : PersonalPronoun := { form := "hamar", person := some .first, number := some .singular }

/-- *hamnii* 'we'. -/
def hamnii : PersonalPronoun := { form := "hamnii", person := some .first, number := some .plural }

/-! ### Second person -/

/-- *tu*, the second person singular nominative of the two lower grades. -/
def tu : PersonalPronoun := { form := "tu", person := some .second, number := some .singular }

/-- *toraa*, the second person singular accusative of the two lower grades. -/
def toraa : PersonalPronoun :=
  { form := "toraa", person := some .second, number := some .singular }

/-- *tor*, the second person singular possessive of the two lower grades. -/
def tor : PersonalPronoun := { form := "tor", person := some .second, number := some .singular }

/-- *apne*, the high honorific second person singular nominative. -/
def apne : PersonalPronoun :=
  { form := "apne", person := some .second, number := some .singular }

/-- *apne-ke*, the high honorific second person singular accusative and possessive. -/
def apneKe : PersonalPronoun :=
  { form := "apne-ke", person := some .second, number := some .singular }

/-- *tohnii*, the second person plural nominative of the two lower grades. -/
def tohnii : PersonalPronoun :=
  { form := "tohnii", person := some .second, number := some .plural }

/-- *tohnii-ke*, the second person plural accusative and possessive of the two lower grades. -/
def tohniiKe : PersonalPronoun :=
  { form := "tohnii-ke", person := some .second, number := some .plural }

/-- *apne-log*, the high honorific second person plural nominative. -/
def apneLog : PersonalPronoun :=
  { form := "apne-log", person := some .second, number := some .plural }

/-- *apne-log-ke*, the high honorific second person plural accusative and possessive. -/
def apneLogKe : PersonalPronoun :=
  { form := "apne-log-ke", person := some .second, number := some .plural }

/-! ### Third person -/

/-- *u*, the third person singular nominative of every grade. -/
def u : PersonalPronoun := { form := "u", person := some .third, number := some .singular }

/-- *okraa*, the nonhonorific third person singular accusative. -/
def okraa : PersonalPronoun :=
  { form := "okraa", person := some .third, number := some .singular }

/-- *okar*, the nonhonorific third person singular possessive. -/
def okar : PersonalPronoun := { form := "okar", person := some .third, number := some .singular }

/-- *unkaa*, the third person singular accusative of the two higher grades. -/
def unkaa : PersonalPronoun :=
  { form := "unkaa", person := some .third, number := some .singular }

/-- *unkar*, the third person singular possessive of the two higher grades. -/
def unkar : PersonalPronoun :=
  { form := "unkar", person := some .third, number := some .singular }

/-- *okhnii*, the third person plural nominative of every grade. -/
def okhnii : PersonalPronoun := { form := "okhnii", person := some .third, number := some .plural }

/-- *okhnii-ke*, the third person plural accusative and possessive of every grade. -/
def okhniiKe : PersonalPronoun :=
  { form := "okhnii-ke", person := some .third, number := some .plural }

/-- The pronoun inventory. -/
def pronouns : Finset PersonalPronoun :=
  {ham, hamraa, hamar, hamnii, tu, toraa, tor, apne, apneKe, tohnii, tohniiKe, apneLog,
    apneLogKe, u, okraa, okar, unkaa, unkar, okhnii, okhniiKe}

/-! ### The pronoun tables -/

/-- The second person singular by case and grade ([alok-2020] Table 2.1). -/
def secondSingular : Case → Grade → PersonalPronoun
  | .nom, .nonhonorific => tu
  | .nom, .honorific => tu
  | .nom, .highHonorific => apne
  | .acc, .nonhonorific => toraa
  | .acc, .honorific => toraa
  | .acc, .highHonorific => apneKe
  | .poss, .nonhonorific => tor
  | .poss, .honorific => tor
  | .poss, .highHonorific => apneKe

/-- The second person plural by case and grade ([alok-2020] Table 2.2). -/
def secondPlural : Case → Grade → PersonalPronoun
  | .nom, .highHonorific => apneLog
  | .nom, _ => tohnii
  | _, .highHonorific => apneLogKe
  | _, _ => tohniiKe

/-- The third person singular by case and grade ([alok-2020] Table 2.3). -/
def thirdSingular : Case → Grade → PersonalPronoun
  | .nom, _ => u
  | .acc, .nonhonorific => okraa
  | .acc, _ => unkaa
  | .poss, .nonhonorific => okar
  | .poss, _ => unkar

/-- The third person plural by case and grade ([alok-2020] Table 2.4). -/
def thirdPlural : Case → Grade → PersonalPronoun
  | .nom, _ => okhnii
  | _, _ => okhniiKe

theorem secondSingular_eq_iff (c : Case) (g h : Grade) :
    secondSingular c g = secondSingular c h ↔
      g = h ∨ g < .highHonorific ∧ h < .highHonorific := by
  revert c g h; decide

theorem thirdSingular_eq_iff (c : Case) (g h : Grade) :
    thirdSingular c g = thirdSingular c h ↔
      c = .nom ∨ g = h ∨ .nonhonorific < g ∧ .nonhonorific < h := by
  revert c g h; decide

theorem isContiguous_tables (c : Case) :
    IsContiguous (secondSingular c) ∧ IsContiguous (secondPlural c) ∧
      IsContiguous (thirdSingular c) ∧ IsContiguous (thirdPlural c) := by
  revert c; unfold IsContiguous; decide

/-! ### Agreement -/

/-- The suffix agreeing with a second person subject at each grade ([alok-2020] Table 3.1). -/
def secondAgreement : Grade → Morph
  | .nonhonorific => .suff "eN"
  | .honorific => .suff "a"
  | .highHonorific => .suff "thi(n)"

theorem secondAgreement_injective : Function.Injective secondAgreement := by decide

/-- The suffix agreeing with a non-second-person subject and with the addressee, by the grade of
each ([alok-2020] Table 3.2). -/
def allocutive : Grade → Grade → Morph
  | .nonhonorific, .nonhonorific => .suff "au"
  | .nonhonorific, .honorific => .suff "o"
  | .nonhonorific, .highHonorific => .suff "ain"
  | _, .highHonorific => .suff "thi(n)"
  | _, _ => .suff "thu(n)"

theorem allocutive_honorific :
    allocutive .honorific = allocutive .highHonorific ∧
      ∀ a b, allocutive .honorific a = allocutive .honorific b ↔
        (a = .highHonorific ↔ b = .highHonorific) := by
  refine ⟨funext fun a ↦ by cases a <;> rfl, ?_⟩
  decide

end Pronouns

end Magahi
