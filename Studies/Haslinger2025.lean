module

public import Mathlib.Order.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Linglib.Semantics.Quantification.Numerals.Roundness
public import Linglib.Pragmatics.Competition
public import Studies.Krifka2007
public import Linglib.Data.Examples.Haslinger2025

/-!
# Haslinger (2025): Pragmatic constraints on imprecision and homogeneity

Haslinger argues that the availability of imprecise construals is regulated not in the lexicon
but by alternatives, through two constraints. No Needless Manner Violations combines two Manner
preferences, for lower structural complexity and for less potential for imprecision, as Pareto
dominance, and blocks a sentence that a potentially p-equivalent alternative dominates. Inference
Preservation blocks an imprecise construal of a subexpression that loses an inference, entailment
or incompatibility, that its precise construal licenses about an alternative.

## Main results

* `lt_complexity_of_lt_potential`: an unblocked expression more imprecise than a competitor is
  strictly simpler, the form–meaning correlation behind *the doors* and *all the doors*.
* `forall_not_violates_iff`: a bare numeral survives Inference Preservation exactly when its
  deviation is under half the lcm of the widths of the scales it lies on, so *99* must be exact
  while *100* tolerates deviations under twenty-five (`ninetyNine_hundred`); that lcm is the
  width of the scale Krifka's hearer infers (`tolerated_deviation_is_inferred_cell`).
* `roundness_depends_on_scales`: *180* is rounder than *200* among angles and *200* than *180*
  among cardinals, (80b,c).
* `conjunction_violates`: a conjunction read non-maximally loses the entailment of its conjuncts.

## Implementation notes

The Manner orderings are read off two natural-number measures on an abstract sentence type, with
potential p-equivalence a relation parameter, since the dissertation's (68) quantifies over
contexts that differ only in the issue parameter. Degree expressions are construals over `ℚ`, the
precise interpretation the exact value and the imprecise one the halo of a contextual deviation
`m`, (69)–(70). The conventionalized scales of §6.2.1 are sets of expressions; here a scale is the
multiples of its width over the numerals' values, given by the widths salient in a context, so
roundness, (22), is `Numerals.Roundness.AtLeastAsRound` over `Numerals.Roundness.OnScale`.
The dissertation's examples are the rows of `Data/Examples/Haslinger2025.json`; its
Ch. 5 extensions to presupposition and redundancy and the collective exceptions of Ch. 7 are not
modelled.

## References

* [haslinger-2025-diss]
* [haslinger-2024]
* [krifka-2007]
* [kriz-spector-2021]
-/

@[expose] public section

namespace Haslinger2025

/-! ### No Needless Manner Violations -/

section Manner

variable {S : Type*} (complexity potential : S → ℕ) (PotEquiv : S → S → Prop)

/-- The Manner profile of a sentence pairs its structural complexity with its potential for
imprecision, the two orderings of (58), combined by the product order as in (57). -/
def manner (φ : S) : ℕ × ℕ := (complexity φ, potential φ)

/-- A cooperative speaker will not use `ψ` when a potentially p-equivalent `φ` is at least as good
on both orderings and better on one, (59): competition among the potentially p-equivalent
sentences along the Manner profile. -/
abbrev Blocked (ψ : S) : Prop :=
  Competition.Blocked (fun ψ ↦ {φ | PotEquiv φ ψ}) (manner complexity potential) ψ

/-- By the form–meaning correlation, an unblocked sentence with more potential for imprecision than
a potentially p-equivalent competitor is strictly simpler than it. -/
theorem lt_complexity_of_lt_potential {φ ψ : S} (h : PotEquiv φ ψ)
    (hp : potential φ < potential ψ) (hb : ¬ Blocked complexity potential PotEquiv ψ) :
    complexity ψ < complexity φ := by
  by_contra hc
  exact hb ⟨φ, h, Prod.lt_iff.mpr (Or.inr ⟨not_lt.mp hc, hp⟩)⟩

end Manner

/-- The sentences of (6) and (8) are the definite plural, the universal quantifier that contains it,
and the hypothetical definite that would contain the quantifier. -/
inductive Plural where
  | the
  | all
  | defAll
  deriving DecidableEq, Repr

/-- In structural complexity *all the doors* contains *the doors*, and the hypothetical (8a)
contains *all doors*. -/
def Plural.complexity : Plural → ℕ
  | .the => 1
  | .all => 2
  | .defAll => 3

/-- The definites have potential for imprecision and the universal quantifier does not. -/
def Plural.potential : Plural → ℕ
  | .the => 1
  | .all => 0
  | .defAll => 1

-- (60)
theorem the_all_incomparable :
    ¬ manner Plural.complexity Plural.potential .the <
        manner Plural.complexity Plural.potential .all ∧
      ¬ manner Plural.complexity Plural.potential .all <
        manner Plural.complexity Plural.potential .the := by
  simp [manner, Prod.lt_iff, Plural.complexity, Plural.potential]

-- (8)
theorem defAll_blocked (PotEquiv : Plural → Plural → Prop) (h : PotEquiv .all .defAll) :
    Blocked Plural.complexity Plural.potential PotEquiv .defAll :=
  ⟨.all, h, by simp [manner, Prod.lt_iff, Plural.complexity, Plural.potential]⟩

/-! ### Inference Preservation -/

/-- A subexpression's precise and imprecise interpretations in a context, as predicates over a
domain of degrees or worlds. -/
structure Construal (D : Type*) where
  precise : D → Prop
  imprecise : D → Prop

/-- `[X]^p` is the truth set of a predicate for `p = true` and its falsity set for `p = false`. -/
def valued {D : Type*} (P : D → Prop) : Bool → D → Prop
  | true => P
  | false => fun d ↦ ¬ P d

instance {D : Type*} (P : D → Prop) [DecidablePred P] (p : Bool) (d : D) :
    Decidable (valued P p d) := by
  cases p <;> simp only [valued] <;> infer_instance

/-- Inference Preservation (18), for one alternative `ψ` of the subexpression `φ`, blocks the use
when, for some truth value, the precise truth of `φ` entails that status of `ψ`, the precise falsity
of `φ` does not, but the imprecise truth of `φ` fails to entail the imprecise status of `ψ`. -/
def Violates {D : Type*} (φ ψ : Construal D) : Prop :=
  ∃ p : Bool, (∀ d, φ.precise d → valued ψ.precise p d) ∧
    ¬ (∀ d, ¬ φ.precise d → valued ψ.precise p d) ∧
    ¬ (∀ d, φ.imprecise d → valued ψ.imprecise p d)

/-! #### Degree expressions (Ch. 6) -/

/-- A bare numeral is read with deviation at most `m`, (69a) and (70a). -/
def numeral (n : ℤ) (m : ℚ) : Construal ℚ := ⟨fun d ↦ d = n, fun d ↦ |d - n| ≤ m⟩

/-- *More than n* is read with deviation at most `m`, (69b) and (70b). -/
def moreThan (n : ℤ) (m : ℚ) : Construal ℚ := ⟨fun d ↦ n < d, fun d ↦ (n : ℚ) - m < d⟩

theorem numeral_violates_of_le {n n' : ℤ} (h : n ≠ n') {m : ℚ}
    (hd : |(n : ℚ) - n'| ≤ 2 * m) : Violates (numeral n m) (numeral n' m) := by
  refine ⟨false, fun d hd' hn' ↦ ?_, fun hall ↦ ?_, fun hall ↦ ?_⟩
  · exact h (Int.cast_injective (hd'.symm.trans hn'))
  · exact (hall (n' : ℚ) (by simp only [numeral]; exact_mod_cast h.symm)) rfl
  · refine hall (((n : ℚ) + n') / 2) ?_ ?_
    · simp only [numeral]
      rw [show ((n : ℚ) + n') / 2 - n = (n' - n) / 2 by ring, abs_div,
        abs_of_pos (by norm_num : (0 : ℚ) < 2), abs_sub_comm]
      linarith
    · show |((n : ℚ) + n') / 2 - n'| ≤ m
      rw [show ((n : ℚ) + n') / 2 - n' = (n - n') / 2 by ring, abs_div,
        abs_of_pos (by norm_num : (0 : ℚ) < 2)]
      linarith

theorem not_numeral_violates_of_lt {n n' : ℤ} (h : n ≠ n') {m : ℚ}
    (hd : 2 * m < |(n : ℚ) - n'|) : ¬ Violates (numeral n m) (numeral n' m) := by
  rintro ⟨p, ha, -, hc⟩
  cases p with
  | true =>
    have := ha n rfl
    simp only [numeral, valued] at this
    exact h (by exact_mod_cast this)
  | false =>
    refine hc fun d hdn hdn' ↦ ?_
    have hdn : |d - n| ≤ m := hdn
    have hdn' : |d - n'| ≤ m := hdn'
    have := abs_sub_le (n : ℚ) d n'
    rw [abs_sub_comm (n : ℚ) d] at this
    linarith

/-! #### Roundness and alternatives (§6.2) -/

section Roundness

open Numerals.Roundness

variable {W : Finset ℤ} {n : ℤ}

/-- The cardinal scales of (15) have widths fifty, twenty-five, ten, five and one. -/
def decimal : Finset ℤ := {50, 25, 10, 5, 1}

/-- The clock-time scales of (16), over minutes after midnight, count quarter hours, five minutes
and minutes. -/
def clock : Finset ℤ := {15, 5, 1}

/-- The angle scales of (17) have widths ninety, ten, five and one degrees. -/
def angle : Finset ℤ := {90, 10, 5, 1}

-- (24)
theorem rounder_examples :
    (AtLeastAsRound (OnScale clock) 646 645 ∧ ¬ AtLeastAsRound (OnScale clock) 645 646) ∧
      AtLeastAsRound (OnScale decimal) 152 150 ∧ ¬ AtLeastAsRound (OnScale decimal) 150 152 := by
  decide

/-- Which of *180* and *200* is rounder depends on the salient scales, *180* among angles and
*200* among cardinals, (80b,c). -/
theorem roundness_depends_on_scales :
    (AtLeastAsRound (OnScale angle) 200 180 ∧ ¬ AtLeastAsRound (OnScale angle) 180 200) ∧
      AtLeastAsRound (OnScale decimal) 180 200 ∧ ¬ AtLeastAsRound (OnScale decimal) 200 180 := by
  decide

theorem twentyFive_ten_incomparable :
    ¬ AtLeastAsRound (OnScale decimal) 25 10 ∧ ¬ AtLeastAsRound (OnScale decimal) 10 25 := by
  decide

/-- A bare numeral with deviation `m` survives Inference Preservation against every rounder
alternative (79a) iff `m` is under half the lcm of its scale widths. -/
theorem forall_not_violates_iff (hW : 0 ∉ W) {m : ℚ} :
    (∀ n' ≠ n, AtLeastAsRound (OnScale W) n n' → ¬ Violates (numeral n m) (numeral n' m)) ↔
      2 * m < scaleLcm W n := by
  have hL := scaleLcm_pos hW n
  constructor
  · intro h
    by_contra hle
    refine h (n + scaleLcm W n) (by omega) (atLeastAsRound_add_scaleLcm W n)
      (numeral_violates_of_le (by omega) ?_)
    push_cast
    rw [sub_add_cancel_left, abs_neg, abs_of_pos (by exact_mod_cast hL)]
    linarith
  · intro hm n' hne h
    refine not_numeral_violates_of_lt hne.symm (lt_of_lt_of_le hm ?_)
    rw [abs_sub_comm, ← Int.cast_sub, ← Int.cast_abs, Int.cast_le]
    exact h.scaleLcm_le_abs_sub hne

/-- *99* lies only on the scale of units, so its imprecise reading is blocked from half a unit of
deviation; *100* lies on every cardinal scale, so its alternatives are the multiples of fifty and
it survives deviations under twenty-five. -/
theorem ninetyNine_hundred {m : ℚ} :
    ((∀ n' ≠ 99, AtLeastAsRound (OnScale decimal) 99 n' →
        ¬ Violates (numeral 99 m) (numeral n' m)) ↔ m < 1 / 2) ∧
      ((∀ n' ≠ 100, AtLeastAsRound (OnScale decimal) 100 n' →
        ¬ Violates (numeral 100 m) (numeral n' m)) ↔ m < 25) := by
  have h99 : scaleLcm decimal 99 = 1 := by decide
  have h100 : scaleLcm decimal 100 = 50 := by decide
  rw [forall_not_violates_iff (by decide), forall_not_violates_iff (by decide), h99, h100]
  constructor <;> constructor <;> intro h <;> push_cast at h ⊢ <;> linarith

open MeasureTheory in
open scoped ENNReal in
/-- Under Krifka's hearer model on aligned salient scales, the deviation a bare numeral
tolerates under Inference Preservation is half the width of the most probable scale for its
report: the dissertation's alternative-based bound is the cell of the scale the hearer
infers. -/
theorem tolerated_deviation_is_inferred_cell
    {μs : Measure W} {ν : Measure ℝ} [SFinite ν] {r : ℝ≥0∞} {I : Set ℝ} {m : ℚ}
    (hν : ∀ ⦃s⦄, MeasurableSet s → s ⊆ I → ν s = r * volume s)
    (hr : r ≠ 0) (hr' : r ≠ ⊤) (hpos : ∀ w ∈ W, 0 < w)
    (hWd : ∀ a ∈ W, ∀ b ∈ W, a ∣ b ∨ b ∣ a)
    (hs : ∀ v w : W, μs {v} = μs {w}) (hs0 : ∀ w : W, μs {w} ≠ 0) (hs' : ∀ w : W, μs {w} ≠ ⊤)
    (hI : ∀ w : W, Set.Ico ((n : ℝ) - (w : ℤ) / 2) ((n : ℝ) + (w : ℤ) / 2) ⊆ I)
    (hne : (W.filter (· ∣ n)).Nonempty) {w : W}
    (hw : ∀ v, (μs.prod ν) (Krifka2007.reportedOn v n) ≤
      (μs.prod ν) (Krifka2007.reportedOn w n)) :
    (∀ n' ≠ n, AtLeastAsRound (OnScale W) n n' → ¬ Violates (numeral n m) (numeral n' m)) ↔
      2 * m < ((w : ℤ) : ℚ) := by
  have hwL := (Krifka2007.coarsest_scale_most_probable μs ν hν hr hr' hpos hWd hs hs0 hs'
    hI hne).1 hw
  rw [forall_not_violates_iff fun h0 ↦ absurd (hpos 0 h0) (lt_irrefl 0), hwL]

end Roundness

-- (69), (70)
theorem moreThan_blocked (n : ℤ) {m : ℚ} (hm : 0 < m) :
    Violates (moreThan n m) (numeral n m) := by
  refine ⟨false, fun d hd ↦ ?_, fun hall ↦ ?_, fun hall ↦ ?_⟩
  · simp only [moreThan, numeral, valued] at hd ⊢
    exact ne_of_gt hd
  · exact (hall (n : ℚ) (lt_irrefl _)) rfl
  · exact hall (n : ℚ) (by show (n : ℚ) - m < n; linarith)
      (by show |(n : ℚ) - n| ≤ m; simp; linarith)

/-! #### Conjunctions (Ch. 7) -/

/-- *Bert, Claire and Dora were there*, (19)–(20), is precisely maximal and imprecisely non-maximal
over the worlds recording who was there. -/
def conjunction : Construal (Fin 3 → Bool) :=
  ⟨fun w ↦ ∀ i, w i = true, fun w ↦ ∃ i, w i = true⟩

/-- A conjunct alternative, *Bert was there*, with no potential for imprecision. -/
def conjunct (i : Fin 3) : Construal (Fin 3 → Bool) :=
  ⟨fun w ↦ w i = true, fun w ↦ w i = true⟩

/-- The non-maximal construal of the conjunction loses the entailment of each conjunct that the
precise construal licenses, so only the maximal construal survives Inference Preservation. -/
theorem conjunction_violates (i : Fin 3) : Violates conjunction (conjunct i) := by
  refine ⟨true, fun w hw ↦ hw i, fun hall ↦ ?_, fun hall ↦ ?_⟩
  · exact Bool.false_ne_true (hall (fun _ ↦ false) (by simp [conjunction]))
  · have hw : conjunction.imprecise (fun j ↦ decide (j ≠ i)) :=
      ⟨if i = 0 then 1 else 0, by fin_cases i <;> decide⟩
    have := hall _ hw
    simp [conjunct, valued] at this

end Haslinger2025
