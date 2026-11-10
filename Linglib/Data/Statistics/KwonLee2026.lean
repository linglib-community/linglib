module

public import Linglib.Data.Statistics.Schema

/-!
# KwonLee2026: statistics (generated)

Auto-generated from `Linglib/Data/Statistics/KwonLee2026.json` by `scripts/gen_statistics.py`.
Do not edit by hand: edit the JSON and re-run the generator.

Three experiments on the Korean null pronoun, the colloquial overt pronoun kyay and a demonstrative
with a noun, each the subject of a target sentence after a context sentence. Experiment 1 rates
naturalness with a sole antecedent; Experiment 2 rates naturalness and asks a comprehension question
where the gender of a noun picks the subject or the object of the context sentence as antecedent;
Experiment 3 rates naturalness and asks for the antecedent where both are of the same gender. Means
and percentages are given as printed, and each contrast with the estimate, standard error, z and
p-value of the mixed model or Holm-adjusted comparison the paper reports for it. The subject-
antecedent shares of earlier studies are those the paper's introduction reports.

## Raw data

* <https://osf.io/8mv2w/files/osfstorage?view_only=53a39b26ad5840469cb969a942c521c3>: data and code
  for all analyses

## References

* [kwon-lee-2026]
-/

@[expose] public section

namespace KwonLee2026

open Data.Statistics

/-- The referring expression in the subject position of the target sentence. -/
inductive Form where
  /-- null pronoun: no overt subject -/
  | nullPro
  /-- overt pronoun: the colloquial gender-neutral third-person pronoun kyay -/
  | overt
  /-- full NP: the demonstrative ku with a noun, as ku chinkwu 'that friend' -/
  | fullNP
  deriving DecidableEq, Repr, Fintype

/-- The antecedent that the context of a setting supplies. -/
inductive Bias where
  /-- subject: the subject of the context sentence -/
  | subject
  /-- object: the object of the context sentence -/
  | object
  deriving DecidableEq, Repr, Fintype

/-- A measure in an experiment, apart for the two context biases of Experiment 2. -/
inductive Setting where
  /-- Experiment 1, naturalness: mean rating from 1 to 7 with a sole antecedent, the topic and
  subject of the context sentence -/
  | exp1Naturalness
  /-- Experiment 2, accuracy, subject-biased: percentage of comprehension questions answered with
  the subject where gender picks the subject -/
  | exp2AccuracySubject
  /-- Experiment 2, accuracy, object-biased: percentage of comprehension questions answered with
  the object where gender picks the object -/
  | exp2AccuracyObject
  /-- Experiment 2, naturalness, subject-biased: mean rating of correctly answered trials where
  gender picks the subject -/
  | exp2NaturalnessSubject
  /-- Experiment 2, naturalness, object-biased: mean rating of correctly answered trials where
  gender picks the object -/
  | exp2NaturalnessObject
  /-- Experiment 3, subject choice: percentage of subject antecedents chosen under global
  ambiguity -/
  | exp3SubjectChoice
  /-- Experiment 3, naturalness: mean rating under global ambiguity -/
  | exp3Naturalness
  deriving DecidableEq, Repr, Fintype

/-- A pair of forms that a contrast compares. -/
inductive Pair where
  /-- null vs. overt pronoun: the null and the overt pronoun -/
  | nullVsOvert
  /-- null pronoun vs. full NP: the null pronoun and the full NP -/
  | nullVsFullNP
  /-- overt pronoun vs. full NP: the overt pronoun and the full NP -/
  | overtVsFullNP
  deriving DecidableEq, Repr, Fintype

/-- A measure of Experiment 2. -/
inductive Measure where
  /-- accuracy: comprehension question accuracy -/
  | accuracy
  /-- naturalness: naturalness rating of correctly answered trials -/
  | naturalness
  deriving DecidableEq, Repr, Fintype

/-- Whether the comprehension question of an Experiment 2 trial was answered as intended. -/
inductive Correctness where
  /-- correct: answered with the antecedent that gender picks -/
  | correct
  /-- incorrect: answered with the other antecedent -/
  | incorrect
  deriving DecidableEq, Repr, Fintype

/-- An earlier study of antecedent choice for null and overt pronouns in globally ambiguous
sentences. -/
inductive Study where
  /-- Carminati (2002): Italian -/
  | carminati2002
  /-- Contemori and Di Domenico (2021), Italian: Italian -/
  | contemoriDiDomenico2021Italian
  /-- Contemori and Di Domenico (2021), Spanish: Spanish -/
  | contemoriDiDomenico2021Spanish
  /-- Zhang and Kwon (2022): Chinese, Experiment 1 -/
  | zhangKwon2022
  /-- Kweon (2011): Korean, with the overt pronoun ku -/
  | kweon2011
  /-- Choe (2021): Korean, with the overt pronouns ku and kunye -/
  | choe2021
  deriving DecidableEq, Repr, Fintype

/-- Participants in Experiment 2. (Section 3.1.1, p. 11; checked against the page images.) -/
def exp2Participants : ℕ := 52

/-- Sets of stimuli in Experiment 2, distributed over its six conditions by a Latin square.
(Section 3.1.2, pp. 11-12; checked against the page images.) -/
def exp2Items : ℕ := 36

/-- A row of Table 1, p. 10; Figure 1, p. 14; Figure 2, p. 15; Figure 3 and Table 5, p. 19: the
mean rating or the percentage of a form in a setting. -/
structure Mean where
  /-- The mean rating, or the percentage. -/
  value : Decimal
  /-- The standard error, where one is printed. -/
  se : Option Decimal
  deriving DecidableEq, Repr

/-- The cells of Table 1, p. 10; Figure 1, p. 14; Figure 2, p. 15; Figure 3 and Table 5, p. 19,
by setting and form; from an experiment; checked against the page images. -/
def means : Setting → Form → Mean
  | .exp1Naturalness, .nullPro => ⟨⟨641, 2⟩, some ⟨4, 2⟩⟩  -- Table 1
  | .exp1Naturalness, .overt => ⟨⟨618, 2⟩, some ⟨45, 3⟩⟩
  | .exp1Naturalness, .fullNP => ⟨⟨623, 2⟩, some ⟨45, 3⟩⟩
  | .exp2AccuracySubject, .nullPro => ⟨⟨929, 1⟩, none⟩  -- Figure 1
  | .exp2AccuracySubject, .overt => ⟨⟨814, 1⟩, none⟩
  | .exp2AccuracySubject, .fullNP => ⟨⟨794, 1⟩, none⟩
  | .exp2AccuracyObject, .nullPro => ⟨⟨603, 1⟩, none⟩
  | .exp2AccuracyObject, .overt => ⟨⟨782, 1⟩, none⟩
  | .exp2AccuracyObject, .fullNP => ⟨⟨795, 1⟩, none⟩
  | .exp2NaturalnessSubject, .nullPro => ⟨⟨458, 2⟩, none⟩  -- Figure 2
  | .exp2NaturalnessSubject, .overt => ⟨⟨462, 2⟩, none⟩
  | .exp2NaturalnessSubject, .fullNP => ⟨⟨433, 2⟩, none⟩
  | .exp2NaturalnessObject, .nullPro => ⟨⟨394, 2⟩, none⟩
  | .exp2NaturalnessObject, .overt => ⟨⟨442, 2⟩, none⟩
  | .exp2NaturalnessObject, .fullNP => ⟨⟨456, 2⟩, none⟩
  | .exp3SubjectChoice, .nullPro =>  -- Figure 3, which prints the object choices as 29.4, 57.2 and 64.7
    ⟨⟨706, 1⟩,
     none⟩
  | .exp3SubjectChoice, .overt => ⟨⟨428, 1⟩, none⟩
  | .exp3SubjectChoice, .fullNP => ⟨⟨353, 1⟩, none⟩
  | .exp3Naturalness, .nullPro =>  -- Table 5; the text gives the standard errors as 0.075, 0.069 and 0.071
    ⟨⟨53, 1⟩,
     some ⟨8, 2⟩⟩
  | .exp3Naturalness, .overt => ⟨⟨53, 1⟩, some ⟨7, 2⟩⟩
  | .exp3Naturalness, .fullNP => ⟨⟨54, 1⟩, some ⟨7, 2⟩⟩

/-- A row of Table 2, p. 10, and p. 9; pp. 14-16; Table 6, p. 20, and p. 19: the contrast between
two forms in a setting: for the null pronoun against another form the simple contrast of the
mixed model or the Holm-adjusted comparison within a context, and for the overt pronoun
against the full NP the Holm-adjusted comparison. -/
structure Contrast where
  /-- The estimate, with the sign printed; none where the paper reports only that the forms do
  not differ. -/
  estimate : Option Decimal
  /-- Its standard error. -/
  se : Option Decimal
  /-- The z value. -/
  z : Option Decimal
  /-- The p-value, none where the paper reports the contrast as not significant without one. -/
  p : Option PValue
  deriving DecidableEq, Repr

/-- The cells of Table 2, p. 10, and p. 9; pp. 14-16; Table 6, p. 20, and p. 19, by setting and
pair; from an experiment; checked against the page images. -/
def contrasts : Setting → Pair → Contrast
  | .exp1Naturalness, .nullVsOvert =>  -- Table 2
    ⟨some ⟨-958, 3⟩,
     some ⟨29, 2⟩,
     some ⟨-336, 2⟩,
     some ⟨.eq, ⟨1, 3⟩⟩⟩
  | .exp1Naturalness, .nullVsFullNP =>
    ⟨some ⟨-762, 3⟩,
     some ⟨29, 2⟩,
     some ⟨-26, 1⟩,
     some ⟨.eq, ⟨9, 3⟩⟩⟩
  | .exp1Naturalness, .overtVsFullNP =>  -- p. 9: n.s.
    ⟨some ⟨19, 2⟩,
     some ⟨19, 2⟩,
     some ⟨101, 2⟩,
     none⟩
  | .exp2AccuracySubject, .nullVsOvert =>  -- p. 14
    ⟨some ⟨1224, 3⟩,
     some ⟨280, 3⟩,
     some ⟨4376, 3⟩,
     some ⟨.eq, ⟨1, 4⟩⟩⟩
  | .exp2AccuracySubject, .nullVsFullNP =>
    ⟨some ⟨1417, 3⟩,
     some ⟨276, 3⟩,
     some ⟨5137, 3⟩,
     some ⟨.lt, ⟨1, 4⟩⟩⟩
  | .exp2AccuracySubject, .overtVsFullNP =>  -- p. 14: no significant differences across all contextual conditions
    ⟨none,
     none,
     none,
     none⟩
  | .exp2AccuracyObject, .nullVsOvert =>
    ⟨some ⟨-1085, 3⟩,
     some ⟨200, 3⟩,
     some ⟨-5438, 3⟩,
     some ⟨.lt, ⟨1, 4⟩⟩⟩
  | .exp2AccuracyObject, .nullVsFullNP =>
    ⟨some ⟨-1216, 3⟩,
     some ⟨205, 3⟩,
     some ⟨-5923, 3⟩,
     some ⟨.lt, ⟨1, 4⟩⟩⟩
  | .exp2AccuracyObject, .overtVsFullNP => ⟨none, none, none, none⟩
  | .exp2NaturalnessSubject, .nullVsOvert =>  -- pp. 15-16
    ⟨some ⟨2, 2⟩,
     some ⟨26, 2⟩,
     some ⟨9, 2⟩,
     some ⟨.eq, ⟨100, 2⟩⟩⟩
  | .exp2NaturalnessSubject, .nullVsFullNP =>
    ⟨some ⟨50, 2⟩,
     some ⟨24, 2⟩,
     some ⟨207, 2⟩,
     some ⟨.eq, ⟨381, 3⟩⟩⟩
  | .exp2NaturalnessSubject, .overtVsFullNP =>  -- p. 16: no significant difference across all context conditions
    ⟨none,
     none,
     none,
     none⟩
  | .exp2NaturalnessObject, .nullVsOvert =>
    ⟨some ⟨-96, 2⟩,
     some ⟨25, 2⟩,
     some ⟨-377, 2⟩,
     some ⟨.eq, ⟨2, 3⟩⟩⟩
  | .exp2NaturalnessObject, .nullVsFullNP =>
    ⟨some ⟨-104, 2⟩,
     some ⟨25, 2⟩,
     some ⟨-424, 2⟩,
     some ⟨.lt, ⟨1, 3⟩⟩⟩
  | .exp2NaturalnessObject, .overtVsFullNP => ⟨none, none, none, none⟩
  | .exp3SubjectChoice, .nullVsOvert =>  -- Table 6
    ⟨some ⟨1745, 3⟩,
     some ⟨180, 3⟩,
     some ⟨969, 2⟩,
     some ⟨.eq, ⟨1, 4⟩⟩⟩
  | .exp3SubjectChoice, .nullVsFullNP =>
    ⟨some ⟨2161, 3⟩,
     some ⟨185, 3⟩,
     some ⟨1168, 2⟩,
     some ⟨.eq, ⟨1, 4⟩⟩⟩
  | .exp3SubjectChoice, .overtVsFullNP =>  -- p. 19, which prints the p-value once as < .015 and once as = .012
    ⟨some ⟨416, 3⟩,
     some ⟨166, 3⟩,
     some ⟨2507, 3⟩,
     some ⟨.eq, ⟨12, 3⟩⟩⟩
  | .exp3Naturalness, .nullVsOvert =>  -- Table 6
    ⟨some ⟨-28, 3⟩,
     some ⟨2, 1⟩,
     some ⟨-14, 2⟩,
     some ⟨.eq, ⟨889, 3⟩⟩⟩
  | .exp3Naturalness, .nullVsFullNP =>
    ⟨some ⟨166, 3⟩,
     some ⟨16, 2⟩,
     some ⟨101, 2⟩,
     some ⟨.eq, ⟨315, 3⟩⟩⟩
  | .exp3Naturalness, .overtVsFullNP =>  -- p. 19: ratings did not differ across the three types
    ⟨none,
     none,
     none,
     none⟩

/-- A row of pp. 14-15: the Holm-adjusted comparison of the subject-biased with the object-biased
context of Experiment 2, for a form on a measure. -/
structure BiasContrast where
  /-- The estimate, with the sign printed. -/
  estimate : Decimal
  /-- Its standard error. -/
  se : Decimal
  /-- The z value. -/
  z : Decimal
  /-- The p-value, none where printed as n.s. -/
  p : Option PValue
  deriving DecidableEq, Repr

/-- The cells of pp. 14-15, by measure and form; from an experiment; checked against the page
images. -/
def biasContrasts : Measure → Form → BiasContrast
  | .accuracy, .nullPro => ⟨⟨-2575, 3⟩, ⟨269, 3⟩, ⟨-9559, 3⟩, some ⟨.lt, ⟨1, 4⟩⟩⟩
  | .accuracy, .overt => ⟨⟨-265, 3⟩, ⟨217, 3⟩, ⟨-122, 2⟩, none⟩
  | .accuracy, .fullNP => ⟨⟨57, 3⟩, ⟨216, 3⟩, ⟨265, 3⟩, none⟩
  | .naturalness, .nullPro => ⟨⟨-106, 2⟩, ⟨35, 2⟩, ⟨-304, 2⟩, some ⟨.eq, ⟨28, 3⟩⟩⟩
  | .naturalness, .overt => ⟨⟨-8, 2⟩, ⟨21, 2⟩, ⟨-37, 2⟩, some ⟨.eq, ⟨100, 2⟩⟩⟩
  | .naturalness, .fullNP => ⟨⟨48, 2⟩, ⟨24, 2⟩, ⟨204, 2⟩, some ⟨.eq, ⟨381, 3⟩⟩⟩

/-- A row of Section 3.2.1, p. 13: the incorrect answers to the comprehension question of
Experiment 2. -/
structure ErrorRate where
  /-- The number of incorrect responses. -/
  errors : ℕ
  /-- The error rate, in percent. -/
  rate : Decimal
  deriving DecidableEq, Repr

/-- The cells of Section 3.2.1, p. 13, by form and bias; from an experiment; checked against the
page images. -/
def exp2Errors : Form → Bias → ErrorRate
  | .nullPro, .subject => ⟨22, ⟨71, 1⟩⟩
  | .nullPro, .object => ⟨124, ⟨397, 1⟩⟩
  | .overt, .subject => ⟨57, ⟨186, 1⟩⟩
  | .overt, .object => ⟨69, ⟨218, 1⟩⟩
  | .fullNP, .subject => ⟨65, ⟨206, 1⟩⟩
  | .fullNP, .object => ⟨63, ⟨205, 1⟩⟩

/-- A row of Section 3.2.2, p. 16: the mean naturalness rating of the Experiment 2 trials
answered as intended and of the others. -/
structure CorrectnessMean where
  /-- The mean rating. -/
  mean : Decimal
  /-- Its standard error. -/
  se : Decimal
  deriving DecidableEq, Repr

/-- The cells of Section 3.2.2, p. 16, by correctness; from an experiment; checked against the
page images. -/
def byCorrectness : Correctness → CorrectnessMean
  | .correct => ⟨⟨440, 2⟩, ⟨4, 2⟩⟩
  | .incorrect =>  -- the effect of correctness: estimate 0.38, SE 0.13, z = 3.05, p = .002
    ⟨⟨405, 2⟩,
     ⟨9, 2⟩⟩

/-- A row of Section 1, pp. 3-5: the antecedent choices of an earlier study, in percent, as the
paper reports them; a share the paper does not report is left out. -/
structure PriorStudy where
  /-- Subject antecedents chosen for the null pronoun. -/
  nullSubject : Decimal
  /-- Subject antecedents chosen for the overt pronoun. -/
  overtSubject : Option Decimal
  /-- Object antecedents chosen for the overt pronoun. -/
  overtObject : Option Decimal
  deriving DecidableEq, Repr

/-- The cells of Section 1, pp. 3-5, by study; from an experiment; checked against the page
images. -/
def priorStudies : Study → PriorStudy
  | .carminati2002 => ⟨⟨8072, 2⟩, none, some ⟨8333, 2⟩⟩  -- p. 3
  | .contemoriDiDomenico2021Italian => ⟨⟨75, 0⟩, none, some ⟨78, 0⟩⟩  -- p. 4
  | .contemoriDiDomenico2021Spanish => ⟨⟨62, 0⟩, none, some ⟨58, 0⟩⟩
  | .zhangKwon2022 => ⟨⟨84, 0⟩, some ⟨653, 1⟩, some ⟨347, 1⟩⟩  -- p. 5
  | .kweon2011 => ⟨⟨811, 1⟩, some ⟨314, 1⟩, some ⟨686, 1⟩⟩
  | .choe2021 => ⟨⟨91, 0⟩, some ⟨73, 0⟩, none⟩

end KwonLee2026
