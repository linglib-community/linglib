module

public import Linglib.Data.Examples.RonderosEtAl2024
public import Linglib.Data.Experiments.RonderosEtAl2024
public import Linglib.Semantics.Degree.Adjective
public import Linglib.Semantics.Reference.Iota
public import Mathlib.Data.Finset.Basic

/-!
# Ronderos et al. (2024): Factors affecting contrastive inferences

A listener who interprets *the short pencil* contrastively, as distinguishing the pencil from a
longer one, identifies the referent before the noun when the display holds such a contrasting
object. Ronderos and colleagues track this contrastive inference by eye-tracking with colour,
scalar and material adjectives, in Sedivy's paradigm, and separate three accounts by their
predictions across adjective types. On Sedivy's pragmatic account the interpretation is
contrastive only for adjectives rarely used descriptively, so colour should show no contrast
effect and material should. On the perceptual account the contrast must be perceived during
preview, and material contrasts are less salient, so colour should show the effect and material
should not. On the semantic account of Aparicio, Xiang and Kennedy a relative gradable adjective
needs a comparison class from the display, which lowers the no-contrast baseline for scalar
adjectives.

## Main statements

* `perceptual_matches`: the perceptual account predicts the effects found.
* `pragmatic_fails`: the pragmatic account does not.
* `baseline_higher_iff_not_relative`: the baseline is higher exactly for the non-gradable
  adjective types.

## Implementation notes

* Kinds of object are named by a representative object. The perceptual factor attributes a
  property to a whole kind as soon as one member shows it, so that objects of a kind are never
  perceived as contrasting.
* Salience and informativity are the paper's premises per adjective type, with size contrasts
  taken as perceptible, as the replicated scalar effect requires.
* The findings are the statistics of the Results section, in
  `Data/Experiments/RonderosEtAl2024.json`, pooled over English, Hindi and Hungarian, which the
  paper's models treat as a grouping unit only. An effect is significant when its printed p-value
  is below 0.05.

## References

* [ronderos-etal-2024]
* [sedivy-etal-1999]
* [sedivy-2003]
* [sedivy-2004]
* [kursat-degen-2021]
* [jara-ettinger-rubio-fernandez-2022]
* [aparicio-xiang-kennedy-2015]
* [kennedy-2007]
-/

@[expose] public section

namespace RonderosEtAl2024

open Data.Experiments

/-! ### The paradigm (Figure 1) -/

/-- The four objects of a display are the target, the object that in the contrast condition is of
the target's kind and lacks the property, the competitor of another kind sharing it, and a
distractor. -/
inductive Object where
  | target
  | contrastingObject
  | competitor
  | distractor
  deriving DecidableEq, Repr, Fintype

/-- A display, as the listener takes it in, records the kind of each object, named by a
representative, and the objects showing the adjective's property. -/
structure Display where
  kind : Object → Object
  has : Finset Object

namespace Display

variable (d : Display)

/-- The descriptive interpretation of the adjective picks out the objects with the property. -/
def descriptive : Finset Object := d.has

/-- The contrastive interpretation picks out the objects with the property that an object of
their kind lacks. -/
def contrastive : Finset Object :=
  d.has.filter fun o ↦ ∃ o', d.kind o' = d.kind o ∧ o' ∉ d.has

theorem contrastive_subset_descriptive : d.contrastive ⊆ d.descriptive := Finset.filter_subset _ _

/-- A property whose contrast is not perceived is taken in by attributing it to a whole kind as
soon as one of its members shows it. -/
def blur : Display where
  kind := d.kind
  has := Finset.univ.filter fun o ↦ ∃ o', d.kind o' = d.kind o ∧ o' ∈ d.has

theorem contrastive_blur : d.blur.contrastive = ∅ := by
  rw [contrastive, Finset.filter_eq_empty_iff]
  rintro o ho ⟨o', hk, hn⟩
  simp only [blur, Finset.mem_filter, Finset.mem_univ, true_and] at ho hn
  obtain ⟨o₁, h₁, hh⟩ := ho
  exact hn ⟨o₁, h₁.trans hk.symm, hh⟩

end Display

/-- An interpretation anticipates the noun when the definite description already refers under
it, and to the target. -/
def Anticipates (S : Finset Object) : Prop := iota (· ∈ S) = some .target

theorem anticipates_iff {S : Finset Object} : Anticipates S ↔ S = {.target} := by
  rw [Anticipates, iota_eq_some_iff, Finset.eq_singleton_iff_unique_mem]

instance (S : Finset Object) : Decidable (Anticipates S) := decidable_of_iff _ anticipates_iff.symm

/-- In the display of the contrast condition the contrasting object is of the target's kind and
lacks the property, and the competitor has it. -/
def contrastDisplay : Display where
  kind
    | .contrastingObject => .target
    | o => o
  has := {.target, .competitor}

/-- In the display of the no-contrast condition the contrasting object is replaced by a
distractor of its own kind. -/
def noContrastDisplay : Display where
  kind o := o
  has := {.target, .competitor}

/-- The display of each condition. -/
def display : Condition → Display
  | .contrast => contrastDisplay
  | .noContrast => noContrastDisplay

theorem contrastive_contrast : contrastDisplay.contrastive = {.target} := by decide

theorem descriptive_contrast : contrastDisplay.descriptive = {.target, .competitor} := by decide

theorem contrastive_noContrast : noContrastDisplay.contrastive = ∅ := by decide

theorem descriptive_noContrast : noContrastDisplay.descriptive = {.target, .competitor} := by
  decide

/-! ### The three factors -/

/-- An adjective type is salient when a contrast in its property is visually salient during
preview. Material contrasts are not ([kursat-degen-2021], [jara-ettinger-rubio-fernandez-2022]),
and colour and size contrasts are. -/
def Salient : AdjType → Prop
  | .material => False
  | .color | .scalar => True

instance : DecidablePred Salient
  | .material => isFalse id
  | .color | .scalar => isTrue trivial

/-- An adjective type is informative when it is rarely used descriptively, so that its use is
expected to be informative. Colour adjectives are produced descriptively about half the time
([sedivy-2004]), material and scalar ones rarely. -/
def Informative : AdjType → Prop
  | .color => False
  | .scalar | .material => True

instance : DecidablePred Informative
  | .color => isFalse id
  | .scalar | .material => isTrue trivial

/-- Scalar adjectives are relative gradable, and colour and material adjectives are non-gradable
([kennedy-2007]). -/
def AdjType.adjectiveClass : AdjType → Degree.AdjectiveClass
  | .scalar => .relative
  | .color | .material => .nonGradable

/-! ### The accounts of the contrast effect -/

/-- An account fixes, per adjective type, how the display is perceived and how the adjective is
interpreted. -/
structure Account where
  perceive : AdjType → Display → Display
  interpret : AdjType → Display → Finset Object

/-- On the pragmatic account ([sedivy-2003], [sedivy-2004]) perception is veridical, and the
adjective is interpreted contrastively only when it is expected to be informative. -/
def pragmatic : Account where
  perceive _ d := d
  interpret t := if Informative t then Display.contrastive else Display.descriptive

/-- On the perceptual account the adjective is always interpreted contrastively, but a contrast
that is not salient is not perceived. -/
def perceptual : Account where
  perceive t d := if Salient t then d else d.blur
  interpret _ := Display.contrastive

/-- An account predicts a contrast effect for an adjective type when the noun is anticipated in
the contrast condition and not in the no-contrast one. -/
def Account.PredictsEffect (a : Account) (t : AdjType) : Prop :=
  Anticipates (a.interpret t (a.perceive t contrastDisplay)) ∧
    ¬ Anticipates (a.interpret t (a.perceive t noContrastDisplay))

instance (a : Account) (t : AdjType) : Decidable (a.PredictsEffect t) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem pragmatic_predictsEffect_iff (t : AdjType) :
    pragmatic.PredictsEffect t ↔ Informative t := by
  cases t <;> decide

theorem perceptual_predictsEffect_iff (t : AdjType) :
    perceptual.PredictsEffect t ↔ Salient t := by
  cases t <;> decide

/-! ### The findings -/

/-- A printed p-value is below 0.05 when it is an upper bound at most 0.05 or a value under
it. -/
def Bound.Significant : Bound → Decimal → Prop
  | .below, p => p.toRat ≤ 5 / 100
  | .exact, p => p.toRat < 5 / 100

instance : ∀ b p, Decidable (Bound.Significant b p)
  | .below, _ => inferInstanceAs (Decidable (_ ≤ _))
  | .exact, _ => inferInstanceAs (Decidable (_ < _))

/-- The paper found a contrast effect for an adjective type when it reports a significant cluster
of condition effects on target looks in the noun window and a significant effect of condition on
the target-advantage score. -/
def Effect (t : AdjType) : Prop :=
  (∃ p ∈ (clusters t).p, Bound.below.Significant p) ∧
    (targetAdvantage t).bound.Significant (targetAdvantage t).p

instance : DecidablePred Effect := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))

/-- Whether looks to the target and the competitor in the no-contrast baseline were significantly
higher for an adjective type than for scalar adjectives, the intercept of the model. -/
def BaselineHigherThanScalar (t : AdjType) : Prop :=
  ∃ r ∈ baselineLooks, r.adjType = t ∧ 0 < r.beta.toRat ∧ r.bound.Significant r.p

instance : DecidablePred BaselineHigherThanScalar := fun _ ↦
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- The perceptual account predicts the effects found, for colour and scalar adjectives and not
for material ones. -/
theorem perceptual_matches : ∀ t, perceptual.PredictsEffect t ↔ Effect t := by decide +kernel

/-- The pragmatic account predicts an effect for material and none for colour, the reverse of
what was found. -/
theorem pragmatic_fails : ¬ ∀ t, pragmatic.PredictsEffect t ↔ Effect t := by decide +kernel

/-- The baseline follows the adjective classes. Looks to the property-matching objects exceed
those for scalar adjectives exactly for the non-gradable types, which need no comparison class
([aparicio-xiang-kennedy-2015]). -/
theorem baseline_higher_iff_not_relative :
    ∀ t, BaselineHigherThanScalar t ↔ t.adjectiveClass ≠ .relative := by
  decide +kernel

theorem salience_not_baseline : ¬ ∀ t, BaselineHigherThanScalar t → Salient t := by
  decide +kernel

end RonderosEtAl2024
