module

public import Linglib.Data.Experiments.BeltramaSchwarz2024
public import Studies.BeltramaSoltBurnett2023
public import Linglib.Semantics.Degree.Granularity
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# Beltrama and Schwarz (2024): Social Stereotypes Affect Imprecision Resolution across Different Tasks

Beltrama and Schwarz describe the speaker of a round numeral as Nerdy, as Chill, or not at all,
and show a phone screen whose number matches the numeral, diverges from it slightly
(Imprecise) or largely. In a Covered Screen task, comprehenders reject the Imprecise screen
more often for Nerdy speakers and less often for Chill ones than at baseline: a persona that
embodies precise speech narrows the numeral's extension (Hypothesis 1). In a Truth Value
Judgment task the Chill effect recurs but Nerdy speakers are rejected as often as the baseline,
which fits neither of the paper's hypotheses for that task. The paper suggests that rejection
is prejudicial there, blaming the speaker, though it then expects every condition to be judged
more charitably, which it does not find.

## Main statements

* `ground_profile_subset_iff`: the traits each persona is introduced with index poles of
  exactly the precision variant it embodies, in the field [beltrama-solt-burnett-2023] measured.
* `Hypothesis1.rejects`, `rejects_imprecise_iff`: Hypothesis 1 as monotonicity of rejection in
  strictness; the Imprecise screen is rejected at the paper's narrow range and accepted at its
  wide one.
* `observed_coveredScreen`, `not_hypothesis2A`, `not_hypothesis2B`: the Covered Screen results
  bear out Hypothesis 1, and the Truth Value Judgment results fit neither Hypothesis 2A nor 2B.
* `PrejudicialAccount.not_agrees`: no table of rejection rates that agrees with the printed
  results satisfies the account of §7.

## Implementation notes

* The precision field is the opposition reading of [beltrama-solt-burnett-2023], precise and
  imprecise speakers occupying opposite quadrants (§2, note 2).
* A persona's profile is read off its traits that are scales of [beltrama-solt-burnett-2023]
  (*articulate*, *uptight*, *laid-back*); the other five traits were not measured there.
* A precision level is a grain width (`Degree.grain`); the ranges of p. 5 are the cells of
  *$200* of widths ten and twenty.
* Rejection rates are only plotted (Figures 3, 6, 8); the results are the paper's verdicts, and
  the account is tested on every table of rates agreeing with them.

## References

* [beltrama-schwarz-2024]
* [beltrama-2018]
* [beltrama-solt-burnett-2023]
* [donofrio-2018]
* [eckert-2008]
* [fiske-cuddy-glick-2007]
* [fricker-2007]
* [krifka-2007]
* [sauerland-stateva-2011]
-/

@[expose] public section

namespace BeltramaSchwarz2024

open SocialMeaning Degree Data.Experiments
open BeltramaSoltBurnett2023 (Variant Factor scales contrastField)

/-! ### The personas -/

/-- The precision field is the opposition [beltrama-solt-burnett-2023] measured. -/
def precisionField : AssociationField Variant Dimension SignType := contrastField .exp1

/-- The evaluation scale of [beltrama-solt-burnett-2023] a trait is, if any. -/
def Descriptor.scale? : Descriptor → Option BeltramaSoltBurnett2023.Scale
  | .articulate => some .articulate
  | .uptight => some .uptight
  | .laidBack => some .laidBack
  | _ => none

/-- The dimension a trait measures, through its scale. -/
def Descriptor.dimension? (x : Descriptor) : Option Dimension :=
  x.scale?.map fun s ↦ Factor.dimension (scales s).dimension

/-- A persona's profile is positive on each dimension one of its traits measures. -/
def profile : AssociationField Persona Dimension SignType :=
  .of fun p d ↦ if ∃ x ∈ (descriptors p).traits, x.dimension? = some d then 1 else 0

/-- The precision variant whose speakers a persona embodies. -/
def Persona.variant : Persona → Variant
  | .nerdy => .precise
  | .chill => .approximate

/-- The traits a persona is introduced with index poles of the variant it embodies, and of no
other (§2, §4.1). -/
theorem ground_profile_subset_iff (p : Persona) (v : Variant) :
    profile.ground.indexes p ⊆ precisionField.ground.indexes v ↔ v = p.variant := by
  revert p v; decide +kernel

/-- The shift of a persona condition toward a stricter interpretation is the sign with which its
variant indexes Competence; the No.Persona baseline does not shift. -/
def personaShift : Option Persona → SignType
  | none => 0
  | some p => precisionField p.variant .competence

@[simp] theorem personaShift_none : personaShift none = 0 := rfl

@[simp] theorem personaShift_nerdy : personaShift (some .nerdy) = 1 := by decide +kernel

@[simp] theorem personaShift_chill : personaShift (some .chill) = -1 := by decide +kernel

theorem personaShift_nerdy_eq_neg_chill :
    personaShift (some .nerdy) = -personaShift (some .chill) :=
  congrFun (BeltramaSoltBurnett2023.antipodal_contrastField .exp1) .competence

-- §3
theorem personaShift_eq_neg_warmth (p : Persona) :
    personaShift (some p) = -precisionField p.variant .warmth := by
  cases p <;> decide +kernel

/-! ### Hypothesis 1 -/

section Level

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]

/-- Hypothesis 1 (p. 5) holds of an assignment of precision levels when the level of a persona
condition narrows as the condition shifts toward strictness. -/
def Hypothesis1 (ε : Option Persona → α) : Prop :=
  ∀ c c', personaShift c ≤ personaShift c' → ε c' ≤ ε c

/-- The imprecise reading of `n` at width `ε` rejects `d` when `d` lies outside the cell of `n`. -/
def Rejects (ε n d : α) : Prop := d ∉ (grain ε).cell n

/-- Around a numeral that is a point of every level, a rejection under a condition is a rejection
under a stricter one. -/
theorem Hypothesis1.rejects {ε : Option Persona → α} (h : Hypothesis1 ε) (hε : ∀ c, 0 < ε c)
    {n d : α} (hn : ∀ c, n ∈ AddSubgroup.zmultiples (ε c)) {c c' : Option Persona}
    (hcc : personaShift c ≤ personaShift c') (hd : Rejects (ε c) n d) : Rejects (ε c') n d :=
  fun hd' ↦ hd (cell_grain_subset_cell_grain (hε c') (h c c' hcc) (hn c') (hn c) hd')

end Level

/-- The width of a range. -/
def RangeRow.width (r : RangeRow) : ℕ := r.upper - r.lower

private theorem cell_grain_200 (k : ℤ) {ε : ℝ} (hk : k * ε = 200) (hε : 0 < ε) :
    (grain ε).cell 200 = Set.Ico (200 - ε / 2) (200 + ε / 2) := by
  rw [cell_grain hε, representative_eq_self_of_mem_zmultiples hε.ne'
    (AddSubgroup.mem_zmultiples_iff.2 ⟨k, by rw [zsmul_eq_mul, hk]⟩)]

/-- The Imprecise screen of Figure 1 is rejected at the narrow range of p. 5 and accepted at the
wide one. -/
theorem rejects_imprecise_iff (r : Range) (hr : r ≠ .exact) :
    Rejects ((ranges r).width : ℝ) uttered (screens .imprecise).displayed.toRat ↔
      r = .narrow := by
  cases r with
  | exact => exact absurd rfl hr
  | narrow =>
    simp only [Rejects, RangeRow.width, ranges, uttered, screens, Decimal.toRat, iff_true]
    rw [show ((205 - 195 : ℕ) : ℝ) = 10 by norm_num, Nat.cast_ofNat,
      cell_grain_200 20 (by norm_num) (by norm_num)]
    norm_num
  | wide =>
    simp only [Rejects, RangeRow.width, ranges, uttered, screens, Decimal.toRat, reduceCtorEq,
      iff_false, not_not]
    rw [show ((210 - 190 : ℕ) : ℝ) = 20 by norm_num, Nat.cast_ofNat,
      cell_grain_200 10 (by norm_num) (by norm_num)]
    norm_num

theorem exact_rejects {γ : ℝ → Set ℝ} (hγ : IsGranularity γ 0) (f : ScreenFit) :
    ((screens f).displayed.toRat : ℝ) ∉ γ uttered ↔ f ≠ .match := by
  rw [isGranularity_zero_iff] at hγ
  subst hγ
  cases f <;> simp [screens, uttered, Decimal.toRat] <;> norm_num

/-! ### The results -/

/-- The direction of a verdict. -/
def Verdict.sign : Verdict → SignType
  | .higher => 1
  | .lower => -1
  | .noDifference => 0

/-- The direction of the rejection rate with a persona against the baseline in a task. -/
def observed (t : Task) (p : Persona) : SignType := (verdicts t p).verdict.sign

/-- Hypothesis 2A (p. 6) holds of the judgment results when rejection shifts as the extension
does. -/
def Hypothesis2A (v : Persona → SignType) : Prop := ∀ p, v p = personaShift (some p)

/-- Hypothesis 2B (pp. 6–7) holds of the judgment results when a speaker invested in accuracy is
trusted, so that rejection shifts against the extension. -/
def Hypothesis2B (v : Persona → SignType) : Prop := ∀ p, v p = -personaShift (some p)

/-- The Covered Screen results bear out Hypothesis 1 for both personas (§4.6). -/
theorem observed_coveredScreen (p : Persona) :
    observed .coveredScreen p = personaShift (some p) := by
  cases p <;> decide +kernel

-- §7
theorem observed_truthValueJudgment_chill :
    observed .truthValueJudgment .chill = personaShift (some .chill) := by decide +kernel

theorem not_hypothesis2A : ¬ Hypothesis2A (observed .truthValueJudgment) :=
  fun h ↦ absurd (h .nerdy) (by decide +kernel)

theorem not_hypothesis2B : ¬ Hypothesis2B (observed .truthValueJudgment) :=
  fun h ↦ absurd (h .nerdy) (by decide +kernel)

/-! ### The prejudiciality account -/

/-- A table of Imprecise rejection rates agrees with the printed results when it orders each
persona against the baseline and each task against the other as the paper reports. -/
def Agrees (r : Task → Option Persona → ℝ) : Prop :=
  (∀ t p, SignType.sign (r t (some p) - r t none) = observed t p) ∧
    ∀ c, ∀ row ∈ taskContrasts, row.persona = c →
      SignType.sign (r .truthValueJudgment c - r .coveredScreen c) = row.verdict.sign

/-- On the account of §7 rejection is prejudicial in a Truth Value Judgment, blaming the speaker
([fricker-2007]), so every condition is rejected less there than in the Covered Screen task, and
Nerdy speakers, taken to be invested in accuracy, so much less that their rise over the baseline
vanishes. -/
structure PrejudicialAccount (r : Task → Option Persona → ℝ) : Prop where
  charitable : ∀ c, r .truthValueJudgment c < r .coveredScreen c
  offset : r .truthValueJudgment (some .nerdy) = r .truthValueJudgment none

theorem PrejudicialAccount.sign_nerdy {r : Task → Option Persona → ℝ} (h : PrejudicialAccount r) :
    SignType.sign (r .truthValueJudgment (some .nerdy) - r .truthValueJudgment none) =
      observed .truthValueJudgment .nerdy := by
  rw [h.offset, sub_self, sign_zero]; decide +kernel

/-- The account's charity is contradicted, the paper finding no task difference in any condition
(§6), as it notes against the account (§7). -/
theorem PrejudicialAccount.not_agrees {r : Task → Option Persona → ℝ} (h : PrejudicialAccount r) :
    ¬ Agrees r := fun ha ↦ by
  have := ha.2 none _ (List.mem_cons_self ..) rfl
  rw [sign_neg (sub_neg.2 (h.charitable none))] at this
  revert this; decide +kernel

end BeltramaSchwarz2024
