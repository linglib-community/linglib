module

public import Linglib.Semantics.Reference.Context.Tower
public import Linglib.Semantics.Reference.Context.Shifts

/-!
# Exclusion features and X-marking

Iatridou analyses the past morphology of counterfactuals as an exclusion feature: the topic's time
or world differs from the speaker's. Over a context tower the speaker's coordinates are those of
the origin and the topic's those of the innermost context, Schlenker's context of thought and
context of utterance, so a world shift produces the modal feature and a temporal shift the
temporal one. Von Fintel and Iatridou call the morphology a language uses to mark non-live
possibilities X-marking, and its absence O-marking.

## Main definitions

* `Modality.Exclusion.ExclF`: the exclusion feature of a context tower.
* `Modality.Exclusion.MarkingStrategy`: X-marking and O-marking.
* `Modality.Exclusion.XMarkingExponent`: a language's X-marking and the morphology it borrows.

## References

* [iatridou-2000]
* [von-fintel-iatridou-2023]
* [schlenker-2004a]
* [mizuno-2024]
-/

@[expose] public section

namespace Modality.Exclusion

open Reference

/-! ### ExclF: the exclusion feature -/

/-- The dimensions along which past morphology excludes. For [iatridou-2000] the temporal and
the modal past are one feature on different coordinates, not a lexical ambiguity. -/
inductive ExclDimension where
  /-- On the temporal dimension the topic's time differs from the speaker's. -/
  | temporal
  /-- On the modal dimension the topic's world differs from the speaker's. -/
  | modal
  deriving DecidableEq, Repr

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- The exclusion feature holds of a context tower on a dimension when the innermost context,
the topic's, differs from the origin, the speaker's, on that coordinate. At a root tower the two
coincide, so neither feature holds. -/
def ExclF (dim : ExclDimension) (tower : ContextTower (Context W E P T)) : Prop :=
  match dim with
  | .temporal => tower.innermost.time ≠ tower.origin.time
  | .modal    => tower.innermost.world ≠ tower.origin.world

/-! ### Shifts produce ExclF -/

/-- A world shift away from the origin's world produces the modal exclusion feature, the
counterfactual use of the past ([iatridou-2000]). -/
theorem worldShift_produces_modal_exclF (c : Context W E P T) (w' : W)
    (h : w' ≠ c.world) :
    ExclF .modal ((ContextTower.root c).push (worldShift w')) :=
  h

/-- A temporal shift away from the origin's time produces the temporal exclusion feature, the
ordinary past. -/
theorem temporalShift_produces_temporal_exclF (c : Context W E P T) (t' : T)
    (h : t' ≠ c.time) :
    ExclF .temporal ((ContextTower.root c).push (temporalShift t')) :=
  h

/-- A world shift followed by a temporal shift produces both exclusion features, the two past
layers of the past counterfactual of [iatridou-2000]. -/
theorem two_shifts_two_exclFs (c : Context W E P T) (w' : W) (t' : T)
    (hw : w' ≠ c.world) (ht : t' ≠ c.time) :
    ExclF .modal (((ContextTower.root c).push (worldShift w')).push (temporalShift t')) ∧
      ExclF .temporal (((ContextTower.root c).push (worldShift w')).push (temporalShift t')) :=
  ⟨hw, ht⟩

/-! ### X-marking / O-marking typology ([von-fintel-iatridou-2023]) -/

/-- The strategies by which a language distinguishes live from non-live possibilities, the
typological labels of [von-fintel-iatridou-2023]. -/
inductive MarkingStrategy where
  /-- X-marking is counterfactual morphology, which expands the domain beyond the live
  possibilities, as in the English Anderson conditional (1a) of [mizuno-2024]. -/
  | xMarking
  /-- O-marking is the absence of X-marking. In the Japanese Anderson conditional (4a) of
  [mizuno-2024] the non-past shifts the time of evaluation back, as the historical present does
  ([schlenker-2004a]). -/
  | oMarking
  deriving DecidableEq, Repr

/-- The complementary marking strategy. O-marking "is generally defined
    as the absence of X-marking" ([mizuno-2024], §2), so the two
    strategies complement each other: in a minimal pair, the alternative
    realizes the `other` of the attested strategy. -/
def MarkingStrategy.other : MarkingStrategy → MarkingStrategy
  | .xMarking => .oMarking
  | .oMarking => .xMarking

@[simp]
theorem MarkingStrategy.other_other : ∀ s : MarkingStrategy, s.other.other = s
  | .xMarking | .oMarking => rfl

/-! ### X-marking exponents ([von-fintel-iatridou-2023] §2, "The form") -/

/-- The morphology realizing X-marking is dedicated or borrowed from the past, imperfective,
future or subjunctive ([von-fintel-iatridou-2023] §2); [mizuno-2024] §4.2 adds the Mandarin
perfective. -/
inductive XMarkingHost where
  /-- Dedicated X-morphology with no other use (Hungarian -nA). -/
  | dedicated
  /-- Fake past ([iatridou-2000]; English, Greek, Romance). -/
  | past
  /-- Fake imperfective (Greek, Romance). -/
  | imperfective
  /-- Future / woll (English would; the Greek and Romance consequent). -/
  | future
  /-- Past subjunctive (German, Icelandic). -/
  | subjunctive
  /-- Perfective ([mizuno-2024], §4.2: Mandarin consequent-final le). -/
  | perfective
  deriving DecidableEq, Repr

/-- A language's X-marking exponent is a citation form with the morphology it borrows, which may
be several pieces, as the Greek past and imperfective are. A fragment records it as `xMarking` in
`Fragments/{Language}/Conditionals.lean`. -/
structure XMarkingExponent where
  /-- The citation form. -/
  form : String
  /-- The morphology the exponent borrows. -/
  components : List XMarkingHost
  deriving DecidableEq, Repr

end Modality.Exclusion
