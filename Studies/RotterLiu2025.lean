module

public import Studies.LiuRotter2025
public import Linglib.Data.Examples.RotterLiu2025
public import Mathlib.Tactic.Ring
public import Linglib.Data.Examples.Readers

/-!
# Rotter and Liu (2025): A Register Approach to Modal (Non-)Concord in English

This file formalizes the second experiment of the paper, which adds a context factor, a close
or a distant interlocutor, to the modal concord design of [liu-rotter-2025]: modal concord
doubles a modal verb with a modal adverb of the same force, *must certainly* and *may
possibly*, against the single modal. The concord analysis of [zeijlstra-2007] predicts no
effect of doubling on speaker commitment for either force, the modal-spread analysis of
[giannakidou-mari-2018] a strengthening for universal modals and no effect for existential
ones (`spreadPred`), so the two differ only on necessity (`analyses_diverge_only_on_necessity`).
The cell means of the paper's tables are rows, and the shifts from the single modal to concord
carry the signs of the first experiment in both contexts: strengthening for necessity, which
adjudicates for spread (`necessity_adjudicates`), and weakening for possibility, which neither
analysis predicts (`possibility_residual`), with confidence tracking commitment and a
force-blind penalty on grammaticality, appropriateness, warmth, friendliness, and education.
The paper's register question is answered by the absence of any number-by-context
interaction: the sign of each concord shift is the same for the close and the distant
interlocutor (`context_invariant`), as an additive context effect must leave it
(`not_registerSensitive_of_main_effect`).

## Implementation notes

The analyses and the observed effects are signs, as in the first experiment's study, whose
`ShiftObservation` and rival accounts are reused. Cell means are rows of
`Data/Examples/RotterLiu2025.json`, hundredths of the 1–7 scale read structurally, so the
observed signs are decided in the kernel; regression estimates are not formal commitments.
Register sensitivity is a difference in sign between the two contexts, and the context main
effect is modelled as one additive shift on both cells of a pair.

## References

* [rotter-liu-2025]
* [liu-rotter-2025]
* [zeijlstra-2007]
* [giannakidou-mari-2018]
-/

@[expose] public section

namespace RotterLiu2025

open Modality (ModalForce)
open LiuRotter2025 (ShiftObservation vacuityEffect spreadEffect forceKey)

/-! ### The two analyses -/

/-- The concord analysis: doubling has no commitment effect for any force. -/
abbrev concordPred : ModalForce → SignType := vacuityEffect

/-- The modal-spread analysis as the paper states it: doubling strengthens commitment for
universal modals and maintains the default for existential ones. -/
def spreadPred : ModalForce → SignType
  | .necessity => 1
  | .weakNecessity => 1
  | .possibility => 0

theorem analyses_diverge_only_on_necessity :
    concordPred .possibility = spreadPred .possibility ∧
      concordPred .necessity ≠ spreadPred .necessity := by
  decide

theorem necessity_adjudicates (o : ShiftObservation) (hf : o.force = .necessity)
    (h : o.smMean < o.mcMean) :
    o.observedSign = spreadPred o.force ∧ o.observedSign ≠ concordPred o.force := by
  have hs : o.observedSign = 1 := by
    show SignType.sign ((o.mcMean : ℤ) - o.smMean) = 1
    exact sign_pos (sub_pos.mpr (by exact_mod_cast h))
  rw [hs, hf]; decide

theorem possibility_residual (o : ShiftObservation) (hf : o.force = .possibility)
    (h : o.mcMean < o.smMean) :
    o.observedSign ≠ spreadPred o.force ∧ o.observedSign ≠ concordPred o.force := by
  have hs : o.observedSign = -1 := by
    show SignType.sign ((o.mcMean : ℤ) - o.smMean) = -1
    exact sign_neg (sub_neg.mpr (by exact_mod_cast h))
  rw [hs, hf]; decide

/-! ### Register sensitivity -/

/-- A concord effect is register-sensitive when its shift differs in sign between the close
and the distant context. -/
def RegisterSensitive (close distant : ShiftObservation) : Prop :=
  close.observedSign ≠ distant.observedSign

theorem context_main_effect_preserves_sign (o : ShiftObservation) (c : ℕ) :
    ShiftObservation.observedSign ⟨o.force, o.mcMean + c, o.smMean + c⟩ = o.observedSign := by
  show SignType.sign (((o.mcMean + c : ℕ) : ℤ) - ((o.smMean + c : ℕ) : ℤ)) =
    SignType.sign ((o.mcMean : ℤ) - o.smMean)
  congr 1; push_cast; ring

theorem not_registerSensitive_of_main_effect (o : ShiftObservation) (c : ℕ) :
    ¬ RegisterSensitive o ⟨o.force, o.mcMean + c, o.smMean + c⟩ := by
  unfold RegisterSensitive
  rw [context_main_effect_preserves_sign]
  simp

/-! ### The cell means -/

/-- The cell of a context, force, and number. -/
def findCell (context force number : String) : Option Datum :=
  Examples.all.find? λ e =>
    decide (e.feature? "context" = some context ∧ e.feature? "force" = some force ∧
      e.feature? "number" = some number)

/-- The observed shift from the single modal to concord on a measure, in a context and under
a force. -/
def observedShift (measure context : String) (force : ModalForce) : Option ShiftObservation := do
  let mc ← findCell context (forceKey force) "MC"
  let sm ← findCell context (forceKey force) "SM"
  pure ⟨force, ← mc.nat? measure, ← sm.nat? measure⟩

/-- The sign of the observed shift. -/
def observedSign (measure context : String) (force : ModalForce) : Option SignType :=
  (observedShift measure context force).map ShiftObservation.observedSign

theorem crossover :
    ∀ measure ∈ ["commitment", "confidence"], ∀ context ∈ ["close", "distant"],
      observedSign measure context .necessity = some 1 ∧
        observedSign measure context .possibility = some (-1) := by
  decide +kernel

theorem penalty :
    ∀ measure ∈ ["grammaticality", "appropriateness", "warmth", "friendliness", "education"],
      ∀ context ∈ ["close", "distant"], ∀ force ∈ [ModalForce.necessity, .possibility],
        observedSign measure context force = some (-1) := by
  decide +kernel

theorem context_invariant :
    ∀ measure ∈ ["commitment", "confidence", "grammaticality", "appropriateness", "warmth",
      "friendliness", "education"],
      ∀ force ∈ [ModalForce.necessity, .possibility],
        observedSign measure "close" force = observedSign measure "distant" force := by
  decide +kernel

/-! ### The first experiment -/

theorem necessity_matches_experiment1 :
    spreadPred .necessity = LiuRotter2025.spreadEffect .necessity := by
  decide

theorem possibility_observed_vs_predicted :
    LiuRotter2025.spreadEffect .possibility ≠ spreadPred .possibility := by
  decide

end RotterLiu2025
