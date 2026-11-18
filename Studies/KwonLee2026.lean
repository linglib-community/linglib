module

public import Linglib.Data.Statistics.KwonLee2026
public import Linglib.Discourse.Accessibility

/-!
# Kwon and Lee (2026): Accessibility Markers in Korean

Korean has a null pronoun, the colloquial overt pronoun *kyay*, and demonstrative phrases such as
*ku chinkwu* 'that friend'. Placed on the Accessibility Marking Scale, the three
[meet its form–function criteria in order](##criteria_strictMono), so Accessibility Theory
predicts that the more accessible the antecedent, here the subject rather than the object of the
preceding sentence, the better the higher form fits it. Three experiments test the prediction
with a sole antecedent, with two antecedents that gender tells apart, and with two that nothing
tells apart. [Every contrast the paper finds has the predicted direction](##found_borne), but
[the overt pronoun and the full noun phrase come apart only under global
ambiguity](##found_iff): elsewhere only the null pronoun differs from the others, and
[only the null pronoun responds to the context](##biasFound_iff). The overt pronoun of the
ambiguous experiment prefers the object, [as in earlier work on Italian, Spanish and Korean, and
unlike two studies of Chinese and Korean](##overt_objectBiased_iff).

## Implementation notes

* *Kyay* is placed at the unstressed-pronoun level, following the paper's argument that this
  contraction of *ku ay* 'that child' is now a third-person pronoun. Korean demonstratives make
  a three-way distinction and Ariel's scale a two-way one; *ku*, which is not speaker-proximate,
  is placed with the distal demonstratives.
* The paper credits *kyay* with more rigidity than the null pronoun, since it is used of
  referents the speaker is familiar with. Ariel's rigidity separates names from other forms and
  from one another, so [it does not separate the three forms](##rigidity_eq), which
  informativity and attenuation do.
* A contrast is found when the p-value printed for it is below .05; one the paper reports only as
  not significant is not found. The printed estimates change sign with the coding of each model,
  so the direction of a contrast is read from the means.
* The accuracy of Experiment 2 is given the prediction the paper states for its naturalness
  ratings, which are those of correctly answered trials. The naturalness ratings of Experiment
  3, taken under whichever reading a participant chose, carry no prediction.
* The earlier studies' figures are those the paper's introduction reports. Where it gives only
  the share of object antecedents for an overt pronoun, the share of subject antecedents is its
  complement.

## TODO

* The stimuli the paper prints are not encoded as examples.
* The earlier studies' figures should come from those studies' own tables once they are
  formalized.

## References

* [kwon-lee-2026]
* [ariel-2001]
* [carminati-2002]
* [contemori-di-domenico-2021]
* [zhang-kwon-2022]
* [kweon-2011]
* [choe-2021]
-/

@[expose] public section

namespace KwonLee2026

open Discourse Data.Statistics

/-! ### The three forms on the scale -/

/-- The level of each form on the Accessibility Marking Scale. -/
def Form.toAccessibility : Form → AccessibilityLevel
  | .nullPro => .zero
  | .overt => .unstressedPron
  | .fullNP => .distalDemNP

/-- The forms ordered by accessibility: `fullNP < overt < nullPro`. -/
instance : LinearOrder Form :=
  LinearOrder.lift' Form.toAccessibility
    fun a b h ↦ by cases a <;> cases b <;> first | rfl | cases h

/-- The three forms meet Ariel's criteria in the order of the scale: each more accessible form is
no more informative or rigid and no less attenuated than the one below it, and differs from it. -/
theorem criteria_strictMono : StrictMono fun f : Form ↦ f.toAccessibility.criteria := by
  intro a b hab
  cases a <;> cases b <;> revert hab <;> simp only [lt_iff_le_not_ge] <;> decide

-- None of the three forms is a name, so rigidity does not tell them apart (p. 21 credits *kyay*
-- with more of it than the null pronoun).
theorem rigidity_eq (f : Form) : f.toAccessibility.rigidity = .nonName := by cases f <;> rfl

/-- The less accessible form of a pair. -/
def Pair.lower : Pair → Form
  | .nullVsOvert => .overt
  | .nullVsFullNP | .overtVsFullNP => .fullNP

/-- The more accessible form of a pair. -/
def Pair.higher : Pair → Form
  | .nullVsOvert | .nullVsFullNP => .nullPro
  | .overtVsFullNP => .overt

theorem Pair.lower_lt_higher (c : Pair) : c.lower < c.higher := by cases c <;> decide

/-! ### What the scale predicts and what the paper finds -/

/-- The mean rating or the percentage of a form in a setting. -/
def Setting.value (s : Setting) (f : Form) : ℚ := (means s f).value.toRat

/-- The antecedent a setting's measure is taken for: the sole antecedent of Experiment 1, a
subject; the one gender picks in Experiment 2; the subject whose choices Experiment 3 counts. -/
def Setting.antecedent : Setting → Option Bias
  | .exp1Naturalness | .exp2AccuracySubject | .exp2NaturalnessSubject | .exp3SubjectChoice =>
    some .subject
  | .exp2AccuracyObject | .exp2NaturalnessObject => some .object
  | .exp3Naturalness => none

/-- The means of a pair bear out the scale: the more accessible form scores higher where the
antecedent is the subject, and lower where it is the object (pp. 8, 11, 17). -/
def Setting.Borne (s : Setting) (c : Pair) : Prop :=
  s.antecedent = some .subject ∧ s.value c.lower < s.value c.higher ∨
    s.antecedent = some .object ∧ s.value c.higher < s.value c.lower

/-- The means of a pair go against the scale. -/
def Setting.Reversed (s : Setting) (c : Pair) : Prop :=
  s.antecedent = some .subject ∧ s.value c.higher < s.value c.lower ∨
    s.antecedent = some .object ∧ s.value c.lower < s.value c.higher

/-- The paper finds a contrast between two forms when the p-value it prints for it is below
.05. -/
def Setting.Found (s : Setting) (c : Pair) : Prop :=
  ∃ p ∈ (contrasts s c).p, p.Significant (1 / 20)

instance (s : Setting) (c : Pair) : Decidable (s.Borne c) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (s : Setting) (c : Pair) : Decidable (s.Reversed c) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (s : Setting) (c : Pair) : Decidable (s.Found c) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The three forms are all told apart only in the antecedent choices of Experiment 3. Elsewhere
the overt pronoun and the full noun phrase never differ, and the null pronoun differs from both
except in the naturalness of a subject antecedent in Experiment 2 and in the naturalness
ratings of Experiment 3 (p. 22). -/
theorem found_iff (s : Setting) (c : Pair) :
    s.Found c ↔ s = .exp3SubjectChoice ∨
      c ≠ .overtVsFullNP ∧ s ≠ .exp2NaturalnessSubject ∧ s ≠ .exp3Naturalness := by
  revert s c; decide +kernel

/-- Every contrast the paper finds has the direction the scale predicts. -/
theorem found_borne {s : Setting} {c : Pair} : s.Found c → s.Borne c := by
  revert s c; decide +kernel

-- The means go against the scale twice, in neither case significantly: with a sole antecedent
-- the full noun phrase is rated above the overt pronoun (p. 9), and with a subject antecedent in
-- Experiment 2 the overt pronoun is rated above the null one.
theorem reversed_iff (s : Setting) (c : Pair) :
    s.Reversed c ↔ s = .exp1Naturalness ∧ c = .overtVsFullNP ∨
      s = .exp2NaturalnessSubject ∧ c = .nullVsOvert := by
  revert s c; decide +kernel

/-! ### Experiment 2: the two contexts -/

/-- The setting of a measure of Experiment 2 in a context. -/
def Measure.setting : Measure → Bias → Setting
  | .accuracy, .subject => .exp2AccuracySubject
  | .accuracy, .object => .exp2AccuracyObject
  | .naturalness, .subject => .exp2NaturalnessSubject
  | .naturalness, .object => .exp2NaturalnessObject

/-- The paper finds an effect of the context on a form when the p-value it prints for the
comparison of the two contexts is below .05. -/
def BiasFound (m : Measure) (f : Form) : Prop :=
  ∃ p ∈ (biasContrasts m f).p, p.Significant (1 / 20)

instance (m : Measure) (f : Form) : Decidable (BiasFound m f) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- In accuracy and in naturalness alike, whether gender picks the subject or the object matters
for the null pronoun and for neither of the other forms (pp. 14–15). -/
theorem biasFound_iff (m : Measure) (f : Form) : BiasFound m f ↔ f = .nullPro := by
  revert m f; decide +kernel

-- The null pronoun does better with the subject on both measures.
theorem nullPro_object_lt_subject (m : Measure) :
    (m.setting .object).value .nullPro < (m.setting .subject).value .nullPro := by
  revert m; decide +kernel

-- Trials answered as intended are rated more natural than the others (p. 16).
theorem incorrect_lt_correct :
    (byCorrectness .incorrect).mean.toRat < (byCorrectness .correct).mean.toRat := by
  decide +kernel

-- Each printed accuracy is the complement of the printed error rate.
theorem accuracy_add_errorRate (f : Form) (b : Bias) :
    (Measure.accuracy.setting b).value f + (exp2Errors f b).rate.toRat = 100 := by
  revert f b; decide +kernel

-- The printed error count gives the printed rate, on the trials of a balanced design, for the
-- null pronoun only.
theorem errorRate_rounds_iff (f : Form) (b : Bias) :
    (exp2Errors f b).rate.RoundsPercent (exp2Errors f b).errors
      (exp2Participants * exp2Items / 6) ↔ f = .nullPro := by
  revert f b; decide +kernel

/-! ### The earlier studies -/

/-- The share of subject antecedents for the null pronoun in an earlier study. -/
def Study.nullSubject (s : Study) : ℚ := (priorStudies s).nullSubject.toRat

/-- The share of subject antecedents for the overt pronoun in an earlier study, the complement of
the share of object antecedents where only that is reported. -/
def Study.overtSubject (s : Study) : Option ℚ :=
  (priorStudies s).overtSubject.map Decimal.toRat <|>
    (priorStudies s).overtObject.map (100 - ·.toRat)

-- In every earlier study, as in Experiment 3, the null pronoun takes the subject more often than
-- the overt one (p. 5).
theorem overtSubject_lt_nullSubject (s : Study) : ∃ o ∈ s.overtSubject, o < s.nullSubject := by
  revert s; decide +kernel

/-- The overt pronoun takes the object more often than the subject in the Italian and Spanish
studies and in Kweon's Korean one, and the subject more often in Zhang and Kwon's Chinese and
Choe's Korean ones (pp. 3–5). -/
theorem overt_objectBiased_iff (s : Study) :
    (∃ o ∈ s.overtSubject, o < 50) ↔ s ≠ .zhangKwon2022 ∧ s ≠ .choe2021 := by
  revert s; decide +kernel

-- *Kyay* sides with the first group, and the null pronoun takes the subject (p. 22).
theorem exp3_overt_lt_half_lt_nullPro :
    Setting.exp3SubjectChoice.value .overt < 50 ∧
      50 < Setting.exp3SubjectChoice.value .nullPro := by
  decide +kernel

end KwonLee2026
