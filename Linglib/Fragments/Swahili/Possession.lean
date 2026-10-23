module

public import Linglib.Fragments.Swahili.Basic

/-!
# Swahili possession

Swahili expresses possession by predication of association, a subject prefix on *na* 'with'
(Ashton pp. 98–99). The present has no verb, *ni-na kisu* 'I have a knife', and the other tenses
put *kuwa* 'be' before *na*, *a-li-ku-wa na watoto wengi* 'he had many children' (p. 144). The
negative takes the negative subject prefix, *si-na kitu* 'I have nothing', and the past negative
*-ku-* in place of *-li-ku-*, *ha-ku-wa na kitu* 'he had nothing'. With a locative class as
subject the construction is the existential, *nje ku-na watu* 'there are some people outside'
(pp. 128–129, 213).

## Main definitions

* `Swahili.Possession.na`: the *na* of association
* `Swahili.Possession.present`, `past`, `negativePast`, `future`: predication of association
  on a subject prefix

## Main results

* `Swahili.Possession.persons`: the affirmative and negative forms of the person cells
* `Swahili.Possession.classes`: forms with class subjects, the negative of class 3 keeping the
  *u-* that the second person singular elides
* `Swahili.Possession.third_singular_past`: *alikuwa na* and *hakuwa na*
* `Swahili.Possession.existential`: Ashton's table of the existential in three tenses

## Implementation notes

*kuwa* is monosyllabic and takes *ku-* after the tense prefixes *-li-* and *-ta-*, which cannot
carry the stress, but not after the past negative *-ku-*, which can (pp. 142–143). The subject
prefix is a list of morphs because the negative is *ha-* before the affirmative prefix.

## References

* [E. O. Ashton, *Swahili Grammar (Including Intonation)* (1947)][ashton-1947]
-/

@[expose] public section

namespace Swahili.Possession

open Swahili Agreement Morphology

/-- The *na* of association, 'with'. -/
def na : Morph := .free "na"

/-- Predication of association in the present, the subject prefix on *na*. -/
def present (s : List Morph) : List Morph := s ++ [na]

/-- Predication of association in the past, *kuwa* with *-li-ku-* before *na*. -/
def past (s : List Morph) : List Morph := s ++ [.pref "li", .pref "ku", .root "wa", na]

/-- The negative of the past, *kuwa* with the past negative *-ku-* before *na*. -/
def negativePast (s : List Morph) : List Morph := s ++ [.pref "ku", .root "wa", na]

/-- Predication of association in the future, *kuwa* with *-ta-ku-* before *na*. -/
def future (s : List Morph) : List Morph := s ++ [.pref "ta", .pref "ku", .root "wa", na]

/-- *Nina*, *una*, *ana*, *tuna*, *mna*, *wana* and their negatives *sina*, *huna*, *hana*,
*hatuna*, *hamna*, *hawana* (pp. 98–99). -/
theorem persons :
    Bundle.personNumberCells.map (fun c ↦
        ((subjectPrefix.realize c).map fun s ↦ Morph.surface (present [s]),
          (negativeSubjectPrefix.realize c).map (Morph.surface ∘ present))) =
      [(some "ni-na", some "si-na"), (some "u-na", some "hu-na"), (some "a-na", some "ha-na"),
        (some "tu-na", some "ha-tu-na"), (some "m-na", some "ha-m-na"),
        (some "wa-na", some "ha-wa-na")] := by
  decide

/-- *-na* 'have' takes each class's subject prefix, as in *ki-na*, *i-na*, *zi-na* and the
negatives, class 3 keeping its *u-* (pp. 98–99, p. 71). -/
theorem classes :
    [NounClass.cl7, .cl9, .cl10].map (fun c ↦ Morph.surface (present [c.subjPrefix])) =
        ["ki-na", "i-na", "zi-na"] ∧
      [NounClass.cl3, .cl9, .cl10].map (fun c ↦ Morph.surface (present c.negSubjPrefix)) =
        ["ha-u-na", "ha-i-na", "ha-zi-na"] ∧
      (subjectPrefix.realize (.personNumber .second .singular)).map (present [·]) =
        some (present [NounClass.cl3.subjPrefix]) ∧
      (negativeSubjectPrefix.realize (.personNumber .second .singular)).map present ≠
        some (present NounClass.cl3.negSubjPrefix) := by
  decide

/-- *Alikuwa na watoto wengi* 'he had many children' and *hakuwa na kitu* 'he hadn't anything'
(p. 144). -/
theorem third_singular_past :
    Morph.surface (past [NounClass.cl1.subjPrefix]) = "a-li-ku-wa na" ∧
      Morph.surface (negativePast NounClass.cl1.negSubjPrefix) = "ha-ku-wa na" := by
  decide

/-- The locative classes 17, 16 and 18 form the existential, *kuna*, *hakuna*, *kulikuwa na* and so
on, in the present, past and future (p. 213). -/
theorem existential :
    [NounClass.cl17, .cl16, .cl18].map (fun c ↦
        [present [c.subjPrefix], present c.negSubjPrefix, past [c.subjPrefix],
          negativePast c.negSubjPrefix, future [c.subjPrefix], future c.negSubjPrefix].map
          Morph.surface) =
      [["ku-na", "ha-ku-na", "ku-li-ku-wa na", "ha-ku-ku-wa na", "ku-ta-ku-wa na",
          "ha-ku-ta-ku-wa na"],
        ["pa-na", "ha-pa-na", "pa-li-ku-wa na", "ha-pa-ku-wa na", "pa-ta-ku-wa na",
          "ha-pa-ta-ku-wa na"],
        ["m-na", "ha-m-na", "m-li-ku-wa na", "ha-m-ku-wa na", "m-ta-ku-wa na",
          "ha-m-ta-ku-wa na"]] := by
  decide

end Swahili.Possession
