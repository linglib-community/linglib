module

public import Linglib.Data.Statistics.Labov2006
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Defs

/-!
# Labov (2006): The Social Stratification of English in New York City

Labov's survey of the Lower East Side measures phonological variables by social class, by
contextual style from casual speech to minimal pairs, and by age. This file
states what the book reads off its printed tables: the stratification of three department
stores, the class and stylistic stratification of every variable except the lower class's (oh),
and the fit of each variable's table of age by class to Labov's models of a stigmatized feature,
stable or changing, and of an incoming prestige feature.

## Implementation notes

* The printed tables are `Data/Statistics/Labov2006.json`. `Variable.toStandard` negates the
  (th) and (dh) indexes, which score stops and affricates above the prestige fricative, so that
  every signed index grows toward the standard.
* The models keep the cells the prose explains: an extreme word puts the lowest or highest class
  at that age's extreme, and a comparative compares the two ages within the middle-ranking
  classes. The lower class gets no age clause, being parenthesized in the model of a changing
  stigmatized feature and flat in the (r) table Labov matches to an incoming prestige feature.
* The deviation predicates use weak order, so the (æh) tie in word lists is no deviation, as the
  book reads it.

## TODO

* Change from below is not formalized: Labov reads (æh) as Case III-B from the lower-class rise
  and (oh) as Case III-A from the ethnic table, and the ethnic table of (æh) is not stored.
* The (r) crossover of the lower middle class appears only in figures over six class groups.

## References

* [labov-2006]
-/

@[expose] public section

namespace Labov2006

open Data.Statistics

/-! ### The scales -/

instance : LinearOrder Store := LinearOrder.lift' Store.ctorIdx (by decide)
instance : LinearOrder Style := LinearOrder.lift' Style.ctorIdx (by decide)
instance : LinearOrder ClassGroup := LinearOrder.lift' ClassGroup.ctorIdx (by decide)
instance : LinearOrder SocioeconomicClass :=
  LinearOrder.lift' SocioeconomicClass.ctorIdx (by decide)
instance : LinearOrder SocialClass := LinearOrder.lift' SocialClass.ctorIdx (by decide)
instance : LinearOrder AehAgeLevel := LinearOrder.lift' AehAgeLevel.ctorIdx (by decide)
instance : LinearOrder OhAgeLevel := LinearOrder.lift' OhAgeLevel.ctorIdx (by decide)

instance : BoundedOrder SocioeconomicClass where
  top := .upperMiddle
  le_top := by decide
  bot := .lower
  bot_le := by decide

instance : BoundedOrder SocialClass where
  top := .sc4
  le_top := by decide
  bot := .sc1
  bot_le := by decide

/-- `a.toLevel` is the age level of the (r) table that the adult age group `a` names. -/
def AgeGroup.toLevel : AgeGroup → AgeLevel
  | .younger => .younger
  | .older => .older

/-! ### The department store survey -/

/-- `anyR1 s` is the percentage of the employees of `s` who used constricted [r] in all or some
positions. -/
def anyR1 (s : Store) : ℕ := (completeResponses s).allR1 + (completeResponses s).someR1

theorem anyR1_strictMono : StrictMono anyR1 := by decide

theorem fourthStops_strictAnti : StrictAnti fun s ↦ (fourthStops s).percent := by decide

/-! ### Class and stylistic stratification -/

/-- `cell v g s` is the printed index of `v` for the class group `g` in the style `s`, if `v` was
measured there. -/
def cell (v : Variable) (g : ClassGroup) : Style → Option Decimal
  | .casual => (classStratification g v).casual
  | .careful => (classStratification g v).careful
  | .reading => (classStratification g v).reading
  | .wordList => (classStratification g v).wordList
  | .minimalPair => (classStratification g v).minimalPair

/-- `v.styles` is the set of styles in which `v` was measured. -/
def Variable.styles (v : Variable) : Set Style := {s | ∀ g, (cell v g s).isSome}

instance (v : Variable) : DecidablePred (· ∈ v.styles) := fun s ↦
  inferInstanceAs (Decidable (∀ g, (cell v g s).isSome))

theorem mem_styles (s : Style) :
    s ∈ Variable.r.styles ∧ (s ∈ Variable.aeh.styles ↔ s ≤ .wordList) ∧
      (s ∈ Variable.oh.styles ↔ s ≤ .wordList) ∧ (s ∈ Variable.th.styles ↔ s ≤ .reading) ∧
      (s ∈ Variable.dh.styles ↔ s ≤ .reading) := by
  cases s <;> decide

/-- `v.toStandard` signs an index of `v` so that it grows toward the prestige form. The (r) index
counts the constricted variant and the vowel indexes grow toward the corrected low vowels, while
the (th) and (dh) indexes score the stop and the affricate above the fricative and are negated. -/
def Variable.toStandard : Variable → ℚ → ℚ
  | .r | .aeh | .oh => id
  | .th | .dh => Neg.neg

/-- `standardIndex v g s` is the signed index of `v` for `g` in `s`, and `0` where nothing was
measured. -/
def standardIndex (v : Variable) (g : ClassGroup) (s : Style) : ℚ :=
  v.toStandard (((cell v g s).map Decimal.toRat).getD 0)

/-- `v` is class stratified in the style `s` when a higher class group is closer to the
standard. -/
def ClassStratified (v : Variable) (s : Style) : Prop := StrictMono fun g ↦ standardIndex v g s

/-- `v` is stylistically stratified in the class group `g` when a more formal style is closer to
the standard. -/
def StyleStratified (v : Variable) (g : ClassGroup) : Prop :=
  StrictMonoOn (standardIndex v g) v.styles

/-- A class group deviates from the class stratification of `v` when the groups are out of
order in some style and the other groups are in order in every style. -/
def ClassDeviant (v : Variable) (g : ClassGroup) : Prop :=
  (∃ s ∈ v.styles, ¬ Monotone fun g' ↦ standardIndex v g' s) ∧
    ∀ s ∈ v.styles, MonotoneOn (fun g' ↦ standardIndex v g' s) {g' | g' ≠ g}

/-- A class group deviates from the stylistic stratification of `v` when its index does not
move toward the standard with formality. -/
def StyleDeviant (v : Variable) (g : ClassGroup) : Prop :=
  ¬ MonotoneOn (standardIndex v g) v.styles

instance (v : Variable) (s : Style) : Decidable (ClassStratified v s) := by
  unfold ClassStratified; infer_instance

instance (v : Variable) (g : ClassGroup) : Decidable (StyleStratified v g) := by
  unfold StyleStratified; infer_instance

instance (v : Variable) (g : ClassGroup) : Decidable (ClassDeviant v g) := by
  unfold ClassDeviant; infer_instance

instance (v : Variable) (g : ClassGroup) : Decidable (StyleDeviant v g) := by
  unfold StyleDeviant; infer_instance

theorem r_stratified :
    (∀ s ∈ Variable.r.styles, ClassStratified .r s) ∧ ∀ g, StyleStratified .r g := by
  decide +kernel

theorem aeh_stratified :
    (∀ g, StyleStratified .aeh g) ∧
      (∀ s ∈ Variable.aeh.styles, s ≠ .wordList → ClassStratified .aeh s) ∧
      Monotone (fun g ↦ standardIndex .aeh g .wordList) ∧
      standardIndex .aeh .lower .wordList = standardIndex .aeh .working .wordList := by
  decide +kernel

theorem th_stratified :
    (∀ s ∈ Variable.th.styles, ClassStratified .th s) ∧ ∀ g, StyleStratified .th g := by
  decide +kernel

theorem dh_stratified :
    (∀ s ∈ Variable.dh.styles, ClassStratified .dh s) ∧ ∀ g, StyleStratified .dh g := by
  decide +kernel

theorem oh_double_deviation :
    ClassDeviant .oh .lower ∧ StyleDeviant .oh .lower ∧ (∀ g ≠ .lower, StyleStratified .oh g) ∧
      ∀ s ∈ Variable.oh.styles,
        StrictMonoOn (fun g ↦ standardIndex .oh g s) {g | g ≠ .lower} := by
  decide +kernel

/-- On the table, a class group deviates from class stratification exactly when it deviates from
stylistic stratification, as Labov's hypothesis has it. -/
theorem classDeviant_iff_styleDeviant (v : Variable) (g : ClassGroup) :
    ClassDeviant v g ↔ StyleDeviant v g := by
  revert v g; decide +kernel

theorem classDeviant_iff (v : Variable) (g : ClassGroup) :
    ClassDeviant v g ↔ v = .oh ∧ g = .lower := by
  revert v g; decide +kernel

/-! ### Apparent time -/

section Cases

variable {κ β : Type*} [LinearOrder κ] [BoundedOrder κ] [Preorder β] (f : AgeGroup → κ → β)

/-- `CaseIA f` says that the use `f` of a feature by age and class is Labov's Case I-A, a
stigmatized feature with no change in progress. The lowest-ranking class uses it most and the
highest least at either age, and the middle-ranking classes use it less as they age. -/
def CaseIA : Prop :=
  (∀ a c, f a c ≤ f a ⊥) ∧ (∀ a c, f a ⊤ ≤ f a c) ∧ ∀ c ∈ Set.Ioo ⊥ ⊤, f .older c < f .younger c

/-- `CaseIB f` says that `f` is Labov's Case I-B, a stigmatized feature with change in
progress. The highest-ranking class uses it least at either age, and the middle-ranking classes
use it more as they age. -/
def CaseIB : Prop := (∀ a c, f a ⊤ ≤ f a c) ∧ ∀ c ∈ Set.Ioo ⊥ ⊤, f .younger c < f .older c

/-- `CaseIIB f` says that `f` is Labov's Case II-B, a prestige feature with change in progress.
The highest-ranking class leads the younger speakers and uses it more when young than when old,
and the middle-ranking classes acquire it as they age. -/
def CaseIIB : Prop :=
  (∀ c, f .younger c ≤ f .younger ⊤) ∧ f .older ⊤ < f .younger ⊤ ∧
    ∀ c ∈ Set.Ioo ⊥ ⊤, f .younger c < f .older c

/-- `ReversesAtTop f` says that below the highest-ranking class the younger speakers use the
feature more than the older, and that the highest class reverses this. -/
def ReversesAtTop : Prop := (∀ c < ⊤, f .older c < f .younger c) ∧ f .younger ⊤ < f .older ⊤

variable {f} in
theorem CaseIA.not_caseIB {c : κ} (hc : c ∈ Set.Ioo ⊥ ⊤) (h : CaseIA f) : ¬ CaseIB f :=
  fun h' ↦ lt_asymm (h.2.2 c hc) (h'.2 c hc)

variable [Fintype κ] [DecidableLT κ] [DecidableLE β] [DecidableLT β]

instance : Decidable (CaseIA f) := by unfold CaseIA; infer_instance
instance : Decidable (CaseIB f) := by unfold CaseIB; infer_instance
instance : Decidable (CaseIIB f) := by unfold CaseIIB; infer_instance
instance : Decidable (ReversesAtTop f) := by unfold ReversesAtTop; infer_instance

end Cases

theorem upgliding_caseIB : CaseIB fun a c ↦ (upglidingByAgeAndClass a c).percent := by decide

/-- (r) in casual speech is distributed as a prestige feature in change, in every detail. -/
theorem r_caseIIB : CaseIIB fun a c ↦ (rCasualByAgeAndClass a.toLevel c).index := by decide

theorem r_gap_widens :
    ((someRCasualByAge .older).upperMiddle : ℤ) - (someRCasualByAge .older).lowerClasses <
      ((someRCasualByAge .younger).upperMiddle : ℤ) - (someRCasualByAge .younger).lowerClasses := by
  decide

theorem aeh_caseIIB : CaseIIB fun a c ↦ (aehByAgeAndClass a c).index := by decide

theorem aeh_lowerClass_monotone : Monotone fun a ↦ (aehLowerClassByAge a).index := by decide

theorem oh_no_case :
    ¬ CaseIA (fun a c ↦ (ohByAgeAndClass a c).index) ∧
      ¬ CaseIB (fun a c ↦ (ohByAgeAndClass a c).index) ∧
      ¬ CaseIIB (fun a c ↦ (ohByAgeAndClass a c).index) := by
  decide

theorem oh_oldest_lowest :
    (∀ a ≠ .age60, (ohByAgeAndEthnicity a).jews < (ohByAgeAndEthnicity .age60).jews ∧
      (ohByAgeAndEthnicity a).italians < (ohByAgeAndEthnicity .age60).italians ∧
      (ohByAgeAndEthnicity a).others < (ohByAgeAndEthnicity .age60).others) ∧
      Monotone fun a ↦ (ohByAgeAndEthnicity a).italians := by
  decide

theorem same_pattern :
    ReversesAtTop (fun a c ↦ (thDhByAgeAndClass a c).th) ∧
      ReversesAtTop (fun a c ↦ (thDhByAgeAndClass a c).dh) ∧
      ReversesAtTop (fun a c ↦ (ingByAgeAndClass a c).casual) := by
  decide

theorem pooled_reversal :
    (pooledLowerClasses .younger).th < (pooledLowerClasses .older).th ∧
      (pooledLowerClasses .younger).dh < (pooledLowerClasses .older).dh ∧
      (∀ c < ⊤, (rCasualByAgeAndClass .younger c).index ≤ (rCasualByAgeAndClass .older c).index) ∧
      (pooledLowerClasses .younger).r < (pooledLowerClasses .older).r := by
  decide

theorem ing_older_less : ∀ c < ⊤,
    (ingByAgeAndClass .older c).casual < (ingByAgeAndClass .younger c).casual ∧
      (ingByAgeAndClass .older c).careful < (ingByAgeAndClass .younger c).careful := by
  decide

/-- (ing) in careful speech is distributed as a stable stigmatized feature. -/
theorem ing_careful_caseIA : CaseIA fun a c ↦ (ingByAgeAndClass a c).careful := by decide

theorem ing_casual_departure :
    (∀ a c, (ingByAgeAndClass a c).casual ≤ (ingByAgeAndClass a ⊥).casual) ∧
      (∀ c ∈ Set.Ioo ⊥ ⊤,
        (ingByAgeAndClass .older c).casual < (ingByAgeAndClass .younger c).casual) ∧
      (∀ c, (ingByAgeAndClass .younger ⊤).casual ≤ (ingByAgeAndClass .younger c).casual) ∧
      (ingByAgeAndClass .older .sc3).casual < (ingByAgeAndClass .older ⊤).casual := by
  decide

end Labov2006
