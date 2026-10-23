/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic.DeriveFintype

/-!
# Judgments

This file defines `Judgment`, the mark a paper puts before an example, the CLDF 1.3
`grammaticalityJudgement` of [forkel-etal-2024]: unmarked, `?`, `??`, `#`, `*`, or `%` for an
example on which speakers differ.

## Main definitions

* `Judgment`: the six marks.
* `Judgment.toPair`: the order embedding that orders the marks, and the `Lattice` on them.
* `Judgment.Band`, `Judgment.band`: the three bands of the severity order that a prediction
  targets.
* `Judgment.ofName?`: the judgment a data file names.

## Implementation notes

* The marks other than `%` are ordered by severity, so `≤` reads "at most as acceptable as" and a
  study writes `.marginal ≤ e.judgment` for an example the paper accepts with at most one question
  mark. The order is a modelling convention rather than a scale from the literature. It ranks `#`
  above `*` because an example marked `#` is well formed but infelicitous; the two constructors
  keep the difference in kind. The mark `%` says that some speakers accept the example and others
  reject it, so it lies above `*` and below the unmarked judgment but is comparable with no mark
  between them; the marks form a lattice, and `⊓` gives the most severe of several.
* A split mark a paper prints, such as `*/??` for speakers who differ, is several marks for one
  sentence. An example records the first as its `judgment` and each further mark as an
  `alsoJudged` paper feature, and a study reading them all reads `Datum.judgments`. Gradient
  ratings are results, recorded in `Data/Experiments/`.

## References

* [forkel-etal-2024]
-/

@[expose] public section

/-- The mark a paper puts before an example. -/
inductive Judgment where
  /-- The paper accepts the example and leaves it unmarked. -/
  | acceptable
  /-- The mark `?` calls the example marginal. -/
  | marginal
  /-- The mark `??` calls the example questionable. -/
  | questionable
  /-- The mark `#` calls the example well formed but infelicitous or semantically anomalous. -/
  | unacceptable
  /-- The mark `*` calls the example ungrammatical. -/
  | ungrammatical
  /-- The mark `%` says that speakers differ, some accepting the example and others rejecting
  it. -/
  | variable
  deriving DecidableEq, Repr, Inhabited, Fintype

namespace Judgment

/-- A mark's position on the severity scale, `ungrammatical` lowest, paired with whether some
speakers accept it; `%` shares the lowest position with `*` and the acceptance of the unmarked
judgment, which places it between the two and beside the marks in between. -/
def toPair : Judgment → Fin 5 × Bool
  | .ungrammatical => (0, false)
  | .unacceptable => (1, false)
  | .questionable => (2, false)
  | .marginal => (3, false)
  | .acceptable => (4, true)
  | .variable => (0, true)

theorem toPair_injective : Function.Injective toPair := by decide

instance : PartialOrder Judgment := PartialOrder.lift toPair toPair_injective

theorem le_iff_toPair_le {j k : Judgment} : j ≤ k ↔ j.toPair ≤ k.toPair := Iff.rfl

instance : DecidableLE Judgment := fun _ _ ↦ decidable_of_iff _ le_iff_toPair_le.symm

instance : DecidableLT Judgment := decidableLTOfDecidableLE

instance : Lattice Judgment where
  sup j k := if j ≤ k then k else if k ≤ j then j else .acceptable
  inf j k := if j ≤ k then j else if k ≤ j then k else .ungrammatical
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

/-- Speakers differ on an example marked `%`, so it is comparable with no mark strictly between
`*` and the unmarked judgment. -/
theorem variable_le_iff {j : Judgment} : .variable ≤ j ↔ j = .variable ∨ j = .acceptable := by
  cases j <;> decide

/-- The three bands of the severity order that a prediction targets: the unmarked judgment, the
middle marks `?` and `%`, on which speakers or grammars divide, and the rejected marks `??`, `#`
and `*`. Which mark a paper prints within a band is its editorial choice, not a prediction. -/
inductive Band where
  | accepted
  | divided
  | rejected
  deriving DecidableEq, Repr

/-- The band of a mark. -/
def band : Judgment → Band
  | .acceptable => .accepted
  | .marginal | .variable => .divided
  | .questionable | .unacceptable | .ungrammatical => .rejected

/-- The band of a two-way prediction: accepted where `p` holds and rejected where it fails. -/
def Band.ofProp (p : Prop) [Decidable p] : Band :=
  if p then .accepted else .rejected

end Judgment

/-- `Judgment.ofName? s` is the judgment the data files write as `s`. -/
def Judgment.ofName? : String → Option Judgment
  | "acceptable" => some .acceptable
  | "marginal" => some .marginal
  | "questionable" => some .questionable
  | "unacceptable" => some .unacceptable
  | "ungrammatical" => some .ungrammatical
  | "variable" => some .variable
  | _ => none
