module

public import Linglib.Semantics.Modality.Typology
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Adverbs
public import Linglib.Data.Examples.LiuRotter2025
public import Mathlib.Basic.Sign.Defs
public import Linglib.Data.Examples.Readers

/-!
# Liu and Rotter (2025): Linguistic and Social Meaning Match

This file formalizes the modal concord experiment of [liu-rotter-2025]. Modal concord doubles
two modal elements of the same force and flavour, *may possibly* and *must certainly*; on
the semantic-vacuity account of [zeijlstra-2007] one element is uninterpretable, so a
concord sentence and its single-modal counterpart should be truth-conditionally identical.
The paper's 2 × 2 (force × number) Latin-square experiment on US English finds concord
non-vacuous, and in opposite directions: doubling strengthens speaker commitment for
necessity and weakens it for possibility, a force × number crossover, as the modal-spread
account of [giannakidou-mari-2018] predicts (`spreadEffect`, `spread_crossover`,
`spread_refutes_vacuity`). Confidence tracks commitment, the match of the title, while
friendliness, warmth, and coolness show a force-blind penalty for doubling
(`warmthEffect`, `warmth_ne_spread`). The observed shifts between the concord and
single-modal cell means carry exactly these signs (`commitment_matches_spread`,
`confidence_matches_spread`, `warmth_matches_penalty`).

## Implementation notes

The effect of concord is a `SignType`; the regression estimates are not formal commitments.
The cell means of the paper's Table 1 are rows of `Data/Examples/LiuRotter2025.json`, stored
as hundredths of the 1–7 scale and read structurally, so the observed signs are decided in
the kernel. The concord precondition, that the doubled elements share a concord class, is read
off the English auxiliary fragment.

## References

* [liu-rotter-2025]
* [zeijlstra-2007]
* [giannakidou-mari-2018]
-/

@[expose] public section

namespace LiuRotter2025

open Modality (ModalForce ModalItem)
open English.Auxiliaries English.Adverbs

/-! ### The concord effect as a force-indexed sign -/

/-- The modal-spread account ([giannakidou-mari-2018]): the modal adverb of a concord
construction is not vacuous; doubling reinforces the force, raising speaker commitment for
necessity and lowering it for possibility. -/
def spreadEffect : ModalForce → SignType
  | .necessity     => 1
  | .weakNecessity => 1
  | .possibility   => -1

/-- The semantic-vacuity account ([zeijlstra-2007]): one modal carries an uninterpretable
feature and contributes no operator, so concord has no commitment effect under any force. -/
def vacuityEffect : ModalForce → SignType := λ _ => 0

@[simp] theorem spreadEffect_necessity : spreadEffect .necessity = 1 := rfl
@[simp] theorem spreadEffect_possibility : spreadEffect .possibility = -1 := rfl
@[simp] theorem vacuityEffect_apply (f : ModalForce) : vacuityEffect f = 0 := rfl

theorem spread_crossover : spreadEffect .necessity ≠ spreadEffect .possibility := by decide

theorem spread_nonvacuous :
    spreadEffect .necessity ≠ 0 ∧ spreadEffect .possibility ≠ 0 := by decide

theorem vacuity_no_interaction (f g : ModalForce) : vacuityEffect f = vacuityEffect g := rfl

theorem spread_refutes_vacuity : spreadEffect ≠ vacuityEffect :=
  λ h => absurd (congrFun h .necessity) (by decide)

/-! ### A second profile: the warmth penalty

The social-meaning measures split in two (Table 5). Confidence, and for necessity formality,
track commitment and show the same crossover; friendliness, warmth, and coolness show a
force-blind main effect of number, the concord sentence rated lower than the single modal
under both forces. -/

/-- The warmth profile: a force-blind penalty for doubling. -/
def warmthEffect : ModalForce → SignType := λ _ => -1

theorem warmth_no_interaction (f g : ModalForce) : warmthEffect f = warmthEffect g := rfl

theorem warmth_real_cost (f : ModalForce) : warmthEffect f ≠ 0 := by
  show (-1 : SignType) ≠ 0; decide

theorem warmth_ne_spread : warmthEffect ≠ spreadEffect :=
  λ h => absurd (congrFun h .necessity) (by decide)

/-! ### The concord precondition in the fragment -/

/-- Two modal items share a concord class when a meaning of each has forces of one class,
both universal or both existential. -/
def SharesConcordForce (a b : ModalItem) : Prop :=
  ∃ x ∈ a.meaning, ∃ y ∈ b.meaning, (x.force.IsUniversal ↔ y.force.IsUniversal)

instance : DecidableRel SharesConcordForce :=
  λ _ _ => inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, (_ ↔ _)))

theorem must_certainly_share :
    SharesConcordForce must.toModalItem certainly := by decide

theorem may_possibly_share :
    SharesConcordForce may.toModalItem possibly := by decide

/-! ### Predicting against the data

The four condition cells carry the Table 1 means of every measure in hundredths of the 1–7
scale. An account predicts the sign of the concord shift, concord minus single modal, per
force; the observed sign is read off the cell means. -/

/-- An observed concord shift for one measure under one force: the concord and single-modal
cell means, in hundredths. -/
structure ShiftObservation where
  force  : ModalForce
  mcMean : ℕ
  smMean : ℕ
  deriving DecidableEq

/-- The observed sign of the concord shift. -/
def ShiftObservation.observedSign (o : ShiftObservation) : SignType :=
  SignType.sign ((o.mcMean : ℤ) - o.smMean)

/-- An account errs on an observation when its predicted sign disagrees with the observed
one. -/
def accountErrs (acc : ModalForce → SignType) (o : ShiftObservation) : Prop :=
  acc o.force ≠ o.observedSign

theorem vacuity_errs_on_shift (o : ShiftObservation) (h : o.mcMean ≠ o.smMean) :
    accountErrs vacuityEffect o := by
  show (0 : SignType) ≠ SignType.sign ((o.mcMean : ℤ) - o.smMean)
  exact (sign_ne_zero.mpr (sub_ne_zero.mpr (by exact_mod_cast h))).symm

theorem spread_correct_of_match (o : ShiftObservation)
    (h : o.observedSign = spreadEffect o.force) : ¬ accountErrs spreadEffect o := by
  simp only [accountErrs, not_not]; exact h.symm

/-- The `force` feature value of a modal force. -/
def forceKey : ModalForce → String
  | .necessity     => "necessity"
  | .weakNecessity => "necessity"
  | .possibility   => "possibility"

/-- The cell with the given force and number (`"MC"` or `"SM"`) values. -/
def findCell (force number : String) : Option Datum :=
  Examples.all.find? λ e =>
    e.feature? "force" == some force && e.feature? "number" == some number

/-- The observed shift of a measure under a force, joining the concord and single-modal
cells. -/
def observedShift (measure : String) (force : ModalForce) : Option ShiftObservation := do
  let mc ← findCell (forceKey force) "MC"
  let sm ← findCell (forceKey force) "SM"
  pure { force := force, mcMean := ← mc.nat? measure, smMean := ← sm.nat? measure }

theorem commitment_matches_spread :
    (observedShift "commitment" .necessity).map (·.observedSign) =
        some (spreadEffect .necessity) ∧
      (observedShift "commitment" .possibility).map (·.observedSign) =
        some (spreadEffect .possibility) := by
  decide

theorem confidence_matches_spread :
    (observedShift "confidence" .necessity).map (·.observedSign) =
        some (spreadEffect .necessity) ∧
      (observedShift "confidence" .possibility).map (·.observedSign) =
        some (spreadEffect .possibility) := by
  decide

theorem warmth_matches_penalty :
    (observedShift "warmth" .necessity).map (·.observedSign) =
        some (warmthEffect .necessity) ∧
      (observedShift "warmth" .possibility).map (·.observedSign) =
        some (warmthEffect .possibility) := by
  decide

end LiuRotter2025
