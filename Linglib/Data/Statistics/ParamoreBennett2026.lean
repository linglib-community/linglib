module

public import Linglib.Data.Statistics.Schema

/-!
# ParamoreBennett2026: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/ParamoreBennett2026.json` by
`scripts/gen_statistics.py`. Do not edit by hand: edit the JSON and re-run the generator.

Oronasal air-pressure recordings of Pakistani Panjabi. Nasalance is the share of nasal air pressure
in the total of oral and nasal air pressure. Experiment 1 compares the vowels of monosyllables with
a contrastive nasal vowel (CṼṼ) and with a vowel before a nasal consonant (CVVN); Experiment 2
compares the glide and the vowel before it in words ending in a vowel, a glide and a contrastive
nasal vowel ([ṼG̃Ṽ=CV]), in an oral vowel ([VGV]), or in a vowel and a nasal consonant ([VGṼN]).
Each table is a linear mixed-effects model with the condition dummy coded, so that an estimate is a
difference from the intercept.

## References

* [paramore-bennett-2026]
-/

@[expose] public section

namespace ParamoreBennett2026

open Data.Statistics

/-- The predictors of the model of the vowel in Experiment 1. -/
inductive VowelPredictor where
  /-- Intercept (CṼṼ): the contrastive nasal vowel, averaged over time steps and vowel qualities -/
  | intercept
  /-- CVVN: the vowel before a nasal consonant -/
  | cvvn
  /-- Beg: the first third of the vowel -/
  | beg
  /-- Mid: the middle third of the vowel -/
  | mid
  /-- Fin: the final third of the vowel -/
  | fin
  /-- uu: the vowel uu -/
  | uu
  /-- ii: the vowel ii -/
  | ii
  /-- oo: the vowel oo -/
  | oo
  /-- ɔɔ: the vowel ɔɔ -/
  | openO
  /-- ee: the vowel ee -/
  | ee
  /-- ɑɑ: the vowel ɑɑ -/
  | aa
  /-- CVVN:Beg: the vowel before a nasal consonant in its first third -/
  | cvvnBeg
  /-- CVVN:Mid: the vowel before a nasal consonant in its middle third -/
  | cvvnMid
  /-- CVVN:Fin: the vowel before a nasal consonant in its final third -/
  | cvvnFin
  deriving DecidableEq, Repr, Fintype

/-- The predictors of the model of the glide in Experiment 2. -/
inductive GlidePredictor where
  /-- Intercept (Final V in [ṼG̃Ṽ=CV]): the final contrastive nasal vowel -/
  | intercept
  /-- glide ([ṼG̃Ṽ=CV] condition): the glide before a contrastive nasal vowel -/
  | nasal
  /-- glide (pre-N [VGṼN] condition): the glide before a vowel that a nasal consonant follows -/
  | preN
  deriving DecidableEq, Repr, Fintype

/-- The predictors of the model of the vowel before the glide in Experiment 2. -/
inductive PenultPredictor where
  /-- Intercept (penult V in oral [VGV]): the vowel before the glide in a word ending in an oral
  vowel -/
  | intercept
  /-- penult V in pre-N [VGṼN]: the vowel before the glide in a word ending in a vowel and a
  nasal consonant -/
  | preN
  /-- penult V in [ṼG̃Ṽ=CV]: the vowel before the glide in a word ending in a contrastive nasal
  vowel -/
  | nasal
  deriving DecidableEq, Repr, Fintype

/-- The half-width of the region of practical equivalence for the nasalance of the contrastive
nasal vowels of Experiment 1, two standard deviations of the speaker who varies least. (§3.5;
checked against the PDF text layer only.) -/
def ropeMonosyllable : Decimal := ⟨61, 3⟩

/-- The half-width of the region of practical equivalence for the nasalance of the final
contrastive nasal vowels of Experiment 2. (§4.2.3; checked against the PDF text layer only.) -/
def ropeFinal : Decimal := ⟨51, 3⟩

/-- The half-width of the region of practical equivalence for the nasalance of the oral vowels
before the glide in Experiment 2. (§4.2.4; checked against the PDF text layer only.) -/
def ropePenult : Decimal := ⟨33, 3⟩

/-- A row of Table 2: a coefficient of the model of mean vowel nasalance in Experiment 1, for
nineteen speakers. -/
structure VowelCoefficient where
  /-- The estimate, a difference in mean nasalance from the intercept. -/
  beta : Decimal
  /-- The lower bound of the 95% confidence interval. -/
  ciLow : Decimal
  /-- The upper bound of the 95% confidence interval. -/
  ciHigh : Decimal
  /-- The t statistic. -/
  t : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of Table 2, by predictor; from an experiment; checked against the page images. -/
def vowelModel : VowelPredictor → VowelCoefficient
  | .intercept => ⟨⟨541, 3⟩, ⟨514, 3⟩, ⟨568, 3⟩, ⟨3955, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .cvvn => ⟨⟨-16, 3⟩, ⟨-39, 3⟩, ⟨7, 3⟩, ⟨-136, 2⟩, ⟨.eq, ⟨18, 2⟩⟩⟩
  | .beg => ⟨⟨-114, 3⟩, ⟨-117, 3⟩, ⟨-112, 3⟩, ⟨-9154, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .mid => ⟨⟨40, 3⟩, ⟨38, 3⟩, ⟨43, 3⟩, ⟨3229, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .fin => ⟨⟨74, 3⟩, ⟨71, 3⟩, ⟨77, 3⟩, ⟨5104, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .uu => ⟨⟨38, 3⟩, ⟨16, 3⟩, ⟨59, 3⟩, ⟨344, 2⟩, ⟨.eq, ⟨2, 3⟩⟩⟩
  | .ii => ⟨⟨52, 3⟩, ⟨21, 3⟩, ⟨82, 3⟩, ⟨334, 2⟩, ⟨.eq, ⟨2, 3⟩⟩⟩
  | .oo => ⟨⟨-46, 3⟩, ⟨-71, 3⟩, ⟨-22, 3⟩, ⟨-366, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .openO => ⟨⟨-9, 3⟩, ⟨-40, 3⟩, ⟨21, 3⟩, ⟨-60, 2⟩, ⟨.eq, ⟨55, 2⟩⟩⟩
  | .ee => ⟨⟨-12, 3⟩, ⟨-61, 3⟩, ⟨37, 3⟩, ⟨-47, 2⟩, ⟨.eq, ⟨64, 2⟩⟩⟩
  | .aa => ⟨⟨-22, 3⟩, ⟨-4, 3⟩, ⟨-4, 3⟩, ⟨-244, 2⟩, ⟨.eq, ⟨2, 2⟩⟩⟩
  | .cvvnBeg => ⟨⟨17, 3⟩, ⟨13, 3⟩, ⟨21, 3⟩, ⟨923, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .cvvnMid => ⟨⟨-2, 3⟩, ⟨-5, 3⟩, ⟨2, 3⟩, ⟨-88, 2⟩, ⟨.eq, ⟨38, 2⟩⟩⟩
  | .cvvnFin => ⟨⟨-15, 3⟩, ⟨-19, 3⟩, ⟨-11, 3⟩, ⟨-727, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩

/-- A row of Table 5: a coefficient of the model of mean glide nasalance in Experiment 2, for the
thirteen speakers who nasalize the vowel before a nasal consonant. -/
structure GlideCoefficient where
  /-- The estimate, a difference in mean nasalance from the final contrastive nasal vowel. -/
  beta : Decimal
  /-- The lower bound of the 95% confidence interval. -/
  ciLow : Decimal
  /-- The upper bound of the 95% confidence interval. -/
  ciHigh : Decimal
  /-- The t statistic. -/
  t : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of Table 5, by predictor; from an experiment; checked against the page images. -/
def glideModel : GlidePredictor → GlideCoefficient
  | .intercept => ⟨⟨538, 3⟩, ⟨475, 3⟩, ⟨600, 3⟩, ⟨1683, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .nasal => ⟨⟨68, 3⟩, ⟨48, 3⟩, ⟨87, 3⟩, ⟨683, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .preN => ⟨⟨-167, 3⟩, ⟨-232, 3⟩, ⟨-100, 3⟩, ⟨-492, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩

/-- A row of Table 6: a coefficient of the model of the mean nasalance of the vowel before the
glide in Experiment 2, for the same thirteen speakers. -/
structure PenultCoefficient where
  /-- The estimate, a difference in mean nasalance from the vowel before the glide in a word
  ending in an oral vowel. -/
  beta : Decimal
  /-- The lower bound of the 95% confidence interval. -/
  ciLow : Decimal
  /-- The upper bound of the 95% confidence interval. -/
  ciHigh : Decimal
  /-- The t statistic. -/
  t : Decimal
  /-- The p-value. -/
  p : PValue
  deriving DecidableEq, Repr

/-- The cells of Table 6, by predictor; from an experiment; checked against the page images. -/
def penultModel : PenultPredictor → PenultCoefficient
  | .intercept => ⟨⟨194, 3⟩, ⟨132, 3⟩, ⟨255, 3⟩, ⟨620, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩
  | .preN => ⟨⟨69, 3⟩, ⟨5, 3⟩, ⟨133, 3⟩, ⟨212, 2⟩, ⟨.eq, ⟨5, 2⟩⟩⟩
  | .nasal => ⟨⟨338, 3⟩, ⟨274, 3⟩, ⟨402, 3⟩, ⟨1036, 2⟩, ⟨.lt, ⟨1, 3⟩⟩⟩

end ParamoreBennett2026
