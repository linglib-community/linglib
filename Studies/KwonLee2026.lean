module

public import Linglib.Discourse.Accessibility
public import Linglib.Fragments.Korean.Pronouns
public import Mathlib.Tactic.NormNum

/-!
# Kwon and Lee (2026): Accessibility Markers in Korean

This file formalizes [kwon-lee-2026]'s three experiments on Korean null pronouns, the
colloquial overt pronoun *kyay*, and demonstrative-plus-noun full NPs as markers on
[ariel-2001]'s Accessibility Marking Scale. `KoreanRefForm` places the three forms on the
substrate's scale and inherits its linear order, so the form–function criteria, more accessible
forms being more attenuated and less informative, are monotonicity statements
(`attenuation_strictMono`, `informativity_antitone`). The paper's central finding, from the
globally ambiguous contexts of Experiment 3, is that subject-antecedent choice increases
strictly with accessibility (`subjectBias_strictMono`), separating the three forms
(`three_way_split`) while naturalness stays flat (`exp3_naturalness_flat`). Experiment 1 finds
the null pronoun most natural with a sole antecedent and no difference between the overt
pronoun and the full NP (`exp1_null_most_natural`, `exp1_overt_fullNP_close`); Experiment 2
finds only the null pronoun sensitive to a context biased against its subject preference, in
comprehension accuracy and in naturalness alike (`exp2_only_null_context_sensitive`,
`exp2_naturalness_only_null_asymmetric`), with trials interpreted as intended rated more
natural (`correct_trials_more_natural`).

The comparison the paper draws in its introduction with Italian ([carminati-2002]), Spanish
([contemori-di-domenico-2021]), Chinese ([zhang-kwon-2022]), and the earlier Korean studies
([kweon-2011], [choe-2021]) is recorded as `CrossLingProfile`s: the null pronoun is more
subject-biased than the overt one in every study (`null_gt_overt_universally`), the spread is
widest in Italian (`italian_widest_spread`), the present overt pronoun is object-biased as in
[kweon-2011] and unlike [choe-2021] (`overt_object_biased_as_kweon`), and in Korean the
null-versus-overt step in bias far exceeds the overt-versus-full-NP step (`null_nonnull_cliff`),
the paper's conclusion that the primary accessibility contrast in Korean is between null and
non-null forms.

## Implementation notes

Percentages are rounded to whole points as the paper reports them, means on the seven-point
scale to hundredths. *Kyay* is placed at the unstressed-pronoun level rather than at a
demonstrative one, following the paper's argument that it has become a third-person pronoun,
and the full NP at the distal-demonstrative-plus-noun level. Subject-bias values of the
comparison studies are complements of the reported object biases where only those are given.

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

open Discourse

/-! ### The three referential forms on the accessibility scale -/

/-- The three Korean referring expressions tested. -/
inductive KoreanRefForm where
  /-- The null pronoun. -/
  | nullPro
  /-- The colloquial gender-neutral third-person pronoun *kyay*. -/
  | overt
  /-- A demonstrative followed by a noun, such as *ku chinkwu* 'that friend'. -/
  | fullNP
  deriving DecidableEq, Repr

/-- The position of each form on the Accessibility Marking Scale. -/
def KoreanRefForm.toAccessibility : KoreanRefForm → AccessibilityLevel
  | .nullPro => .zero
  | .overt => .unstressedPron
  | .fullNP => .distalDemNP

/-- The accessibility rank of a form. -/
@[simp] def KoreanRefForm.rank (f : KoreanRefForm) : ℕ := f.toAccessibility.rank

/-- The forms ordered by accessibility: `fullNP < overt < nullPro`. -/
instance : LinearOrder KoreanRefForm :=
  LinearOrder.lift' KoreanRefForm.rank
    (λ a b h => by cases a <;> cases b <;>
      simp_all [KoreanRefForm.toAccessibility, AccessibilityLevel.rank])

theorem fullNP_lt_overt : (KoreanRefForm.fullNP : KoreanRefForm) < .overt := by decide

theorem overt_lt_nullPro : (KoreanRefForm.overt : KoreanRefForm) < .nullPro := by decide

/-- The surface form: the overt pronoun is the fragment's *gyae*; the full NP varies with the
item. -/
def KoreanRefForm.surface : KoreanRefForm → Option String
  | .nullPro => none
  | .overt => some Korean.Pronouns.gyae.form
  | .fullNP => some "ku chinkwu"

theorem attenuation_strictMono :
    StrictMono (λ f : KoreanRefForm => f.toAccessibility.attenuation) := by
  intro a b hab; cases a <;> cases b <;> revert hab <;> decide

theorem informativity_antitone :
    Antitone (λ f : KoreanRefForm => f.toAccessibility.informativity) := by
  intro a b hab; cases a <;> cases b <;> revert hab <;> decide

/-! ### Experiment 3: antecedent choice under global ambiguity -/

/-- Antecedent choice for one form, as percentages of subject and object choices (Figure 3). -/
structure AntecedentChoice where
  /-- The form. -/
  form : KoreanRefForm
  /-- The percentage of subject-antecedent choices. -/
  subjectPercent : ℕ
  /-- The percentage of object-antecedent choices. -/
  objectPercent : ℕ
  deriving Repr

/-- The null pronoun: 70.6% subject choices. -/
def exp3_pro : AntecedentChoice := ⟨.nullPro, 71, 29⟩

/-- *Kyay*: 42.8% subject choices. -/
def exp3_overt : AntecedentChoice := ⟨.overt, 43, 57⟩

/-- The full NP: 35.3% subject choices. -/
def exp3_fullNP : AntecedentChoice := ⟨.fullNP, 35, 65⟩

/-- Subject-antecedent bias by form. -/
@[simp] def subjectBias : KoreanRefForm → ℕ
  | .nullPro => exp3_pro.subjectPercent
  | .overt => exp3_overt.subjectPercent
  | .fullNP => exp3_fullNP.subjectPercent

/-- Object-antecedent bias by form. -/
@[simp] def objectBias : KoreanRefForm → ℕ
  | .nullPro => exp3_pro.objectPercent
  | .overt => exp3_overt.objectPercent
  | .fullNP => exp3_fullNP.objectPercent

theorem exp3_partitions (f : KoreanRefForm) : subjectBias f + objectBias f = 100 := by
  cases f <;> decide

theorem subjectBias_strictMono : StrictMono subjectBias := by
  intro a b hab; cases a <;> cases b <;> revert hab <;> decide

theorem objectBias_strictAnti : StrictAnti objectBias := by
  intro a b hab; cases a <;> cases b <;> revert hab <;> decide

theorem three_way_split : Function.Injective subjectBias :=
  subjectBias_strictMono.injective

/-- Mean naturalness on the seven-point scale (Table 5). -/
def exp3_naturalness : KoreanRefForm → ℚ
  | .nullPro => 53/10
  | .overt => 53/10
  | .fullNP => 54/10

theorem exp3_naturalness_flat (f g : KoreanRefForm) :
    exp3_naturalness f - exp3_naturalness g ≤ 1/10 := by
  cases f <;> cases g <;> norm_num [exp3_naturalness]

/-! ### Experiment 1: a sole antecedent -/

/-- Mean naturalness on the seven-point scale with a single available antecedent (Table 1). -/
def exp1_naturalness : KoreanRefForm → ℚ
  | .nullPro => 641/100
  | .overt => 618/100
  | .fullNP => 623/100

theorem exp1_null_most_natural :
    exp1_naturalness .overt < exp1_naturalness .nullPro ∧
      exp1_naturalness .fullNP < exp1_naturalness .nullPro := by
  norm_num [exp1_naturalness]

theorem exp1_overt_fullNP_close :
    exp1_naturalness .fullNP - exp1_naturalness .overt ≤ 1/10 := by
  norm_num [exp1_naturalness]

/-! ### Experiment 2: a context biased toward the subject or the object -/

/-- One form's results in Experiment 2: comprehension accuracy (Figure 1, in percent) and mean
naturalness (Figure 2) under a subject-biased and under an object-biased context. -/
structure Exp2Result where
  /-- The form. -/
  form : KoreanRefForm
  /-- Accuracy under a subject-biased context. -/
  subjectAccuracy : ℕ
  /-- Accuracy under an object-biased context. -/
  objectAccuracy : ℕ
  /-- Naturalness under a subject-biased context. -/
  subjectNaturalness : ℚ
  /-- Naturalness under an object-biased context. -/
  objectNaturalness : ℚ
  deriving Repr

/-- The null pronoun: 92.9% against 60.3% accuracy, 4.58 against 3.94 naturalness. -/
def exp2_pro : Exp2Result := ⟨.nullPro, 93, 60, 458/100, 394/100⟩

/-- *Kyay*: 81.4% against 78.2% accuracy, 4.62 against 4.42 naturalness. -/
def exp2_overt : Exp2Result := ⟨.overt, 81, 78, 462/100, 442/100⟩

/-- The full NP: 79.4% against 79.5% accuracy, 4.33 against 4.56 naturalness. -/
def exp2_fullNP : Exp2Result := ⟨.fullNP, 79, 80, 433/100, 456/100⟩

/-- The accuracy gap between the two contexts. -/
def Exp2Result.accuracyGap (r : Exp2Result) : ℕ :=
  max r.subjectAccuracy r.objectAccuracy - min r.subjectAccuracy r.objectAccuracy

/-- The naturalness gap between the two contexts. -/
def Exp2Result.naturalnessGap (r : Exp2Result) : ℚ :=
  max r.subjectNaturalness r.objectNaturalness - min r.subjectNaturalness r.objectNaturalness

/-- Only the null pronoun resists a context biased against its subject preference: its
accuracy drops by over thirty points while the other forms move by at most five. -/
theorem exp2_only_null_context_sensitive :
    30 < exp2_pro.accuracyGap ∧ exp2_overt.accuracyGap ≤ 5 ∧ exp2_fullNP.accuracyGap ≤ 5 := by
  decide

theorem exp2_naturalness_only_null_asymmetric :
    1/2 < exp2_pro.naturalnessGap ∧ exp2_overt.naturalnessGap ≤ 1/4 ∧
      exp2_fullNP.naturalnessGap ≤ 1/4 := by
  norm_num [Exp2Result.naturalnessGap, exp2_pro, exp2_overt, exp2_fullNP]

/-- Mean naturalness of trials answered as intended, 4.40, and of the others, 4.05. -/
def correctTrialNaturalness : ℚ := 440/100
def incorrectTrialNaturalness : ℚ := 405/100

theorem correct_trials_more_natural : incorrectTrialNaturalness < correctTrialNaturalness := by
  norm_num [correctTrialNaturalness, incorrectTrialNaturalness]

/-! ### The cross-linguistic comparison -/

/-- A study's subject-antecedent bias for the null and the overt pronoun under global
ambiguity, in percent. -/
structure CrossLingProfile where
  /-- The language and study. -/
  study : String
  /-- Subject choices for the null pronoun. -/
  nullSubject : ℕ
  /-- Subject choices for the overt pronoun. -/
  overtSubject : ℕ
  deriving Repr

/-- Italian ([carminati-2002]): 80.72% subject for the null pronoun, 83.33% object for the
overt one. -/
def italian : CrossLingProfile := ⟨"Italian", 81, 17⟩

/-- Spanish ([contemori-di-domenico-2021]): 62% subject for the null pronoun, 58% object for
the overt one. -/
def spanish : CrossLingProfile := ⟨"Spanish", 62, 42⟩

/-- Chinese ([zhang-kwon-2022]): 84% and 65.3% subject. -/
def chinese : CrossLingProfile := ⟨"Chinese", 84, 65⟩

/-- Korean with *kyay*, Experiment 3. -/
def korean : CrossLingProfile :=
  ⟨"Korean", exp3_pro.subjectPercent, exp3_overt.subjectPercent⟩

/-- Korean with *ku* and *kunye* ([kweon-2011]): 81.1% and 31.4% subject. -/
def koreanKweon : CrossLingProfile := ⟨"Korean (Kweon 2011)", 81, 31⟩

/-- Korean with *ku* and *kunye* ([choe-2021]): 91% and 73% subject. -/
def koreanChoe : CrossLingProfile := ⟨"Korean (Choe 2021)", 91, 73⟩

/-- The studies compared. -/
def profiles : List CrossLingProfile :=
  [italian, spanish, chinese, korean, koreanKweon, koreanChoe]

theorem null_gt_overt_universally : ∀ p ∈ profiles, p.overtSubject < p.nullSubject := by
  decide

/-- The spread between the two pronouns. -/
def CrossLingProfile.spread (p : CrossLingProfile) : ℕ := p.nullSubject - p.overtSubject

theorem italian_widest_spread :
    spanish.spread < italian.spread ∧ chinese.spread < italian.spread ∧
      korean.spread < italian.spread := by
  decide

theorem overt_object_biased_as_kweon :
    korean.overtSubject < 50 ∧ koreanKweon.overtSubject < 50 ∧ 50 < koreanChoe.overtSubject := by
  decide

/-- The spread in subject bias between two forms of Experiment 3. -/
def biasSpread (a b : AntecedentChoice) : ℕ :=
  max a.subjectPercent b.subjectPercent - min a.subjectPercent b.subjectPercent

theorem null_nonnull_cliff :
    3 * biasSpread exp3_overt exp3_fullNP < biasSpread exp3_pro exp3_overt := by
  decide

end KwonLee2026
