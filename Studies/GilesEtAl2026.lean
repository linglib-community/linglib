module

public import Mathlib.Order.MinMax
public import Linglib.Data.Examples.GilesEtAl2026
public import Linglib.Data.Examples.Readers

/-!
# Giles, Rubio-Fernandez and Mollica (2026): Search Efficiency Drives Reference Production Across Modalities, But Colour Is Special

This file formalizes the search-efficiency view of overinformative reference as [giles-etal-2026]
test it across attributes and sensory modalities. On that view ([rubio-fernandez-2019],
[jara-ettinger-rubio-fernandez-2022]) a speaker adds a redundant modifier when it speeds the
listener's search for the referent, and a description guides search along the most discriminable
attribute it mentions (`Display.efficiency`); so a redundant attribute exerts a pressure to
overinform exactly when it is more discriminable than the attribute that already singles out the
target (`Display.Pressure`, `Display.pressure_iff`). The three display types of the first
experiment, built from the two calibration points the psychophysical staircases deliver, come out
as the paper predicts: pressure when the sufficient attribute is hard and the redundant one easy,
none when both are easy or the redundant one is hard (`predicted_sHighRLow`, `predicted_baseline`).
The rival strategy of mentioning every highly discriminable attribute ([fukumura-carminati-2022])
cannot tell the baseline from the critical display (`highRedundant_predicted_baseline`), and the
baseline contrast decides between the two (`rows_baseline_refutes_highRedundant`).

Any strategy that reads only the display predicts no difference between two redundant attributes
at matched discriminability (`predictedBy_self`). The data contradict this twice: redundant colour
is used more than redundant material in the first experiment and more than redundant orientation
in the second, where attentional guidance, production effort and term frequency are controlled
(`rows_colour_special`), while low- and high-frequency colour terms do not differ
(`rows_frequency_predicted`).

## Implementation notes

* Discriminability is the two-point scale the adaptive staircases produce for each participant
  and attribute (`Discriminability`); the model is stated for any linear order so that graded
  measures fit it too.
* A row is one non-reference level of one predictor of the paper's regressions (Tables 1 and 2);
  its observed direction against the reference level is the side of zero its 95% credible
  interval lies on (`Row.observed`), and the coefficients stay in the data rows.
* In the second experiment the sufficient attribute is the shape noun, which was never at a
  category boundary, so both attributes count as highly discriminable there.
* The paper's speculations about why colour is privileged, optimised category partitions and
  learned strategy selection, are not modelled; nor are display density and contextual
  distinctiveness, which the second experiment varied without finding an effect.

## References

* [giles-etal-2026]
* [rubio-fernandez-2019]
* [jara-ettinger-rubio-fernandez-2022]
* [fukumura-carminati-2022]
* [kursat-degen-2021]
* [degen-etal-2020]
* [wolfe-horowitz-2017]
-/

@[expose] public section

namespace GilesEtAl2026


variable {D : Type*}

/-! ### Displays and the predictions of a production strategy -/

/-- A display as the speaker's choice sees it: the perceptual discriminability of the attribute
that alone singles out the target and that of the redundant attribute. -/
structure Display (D : Type*) where
  /-- Discriminability of the sufficient attribute. -/
  sufficient : D
  /-- Discriminability of the redundant attribute. -/
  redundant : D
  deriving DecidableEq

/-- The speaker's options: the sufficient attribute alone, or both attributes. -/
inductive Description
  | minimal
  | overinformative
  deriving DecidableEq

/-- The direction of a level against its reference level. -/
inductive Direction
  | lower
  | higher
  | null
  deriving DecidableEq, Repr

/-- The direction a production strategy predicts for a level against its reference, given the
condition `P` under which the strategy overinforms. -/
def predictedBy (P : Display D → Prop) [DecidablePred P] (level ref : Display D) : Direction :=
  if P level then (if P ref then .null else .higher) else (if P ref then .lower else .null)

variable {P : Display D → Prop} [DecidablePred P] {level ref : Display D}

theorem predictedBy_eq_null (h : P level ↔ P ref) : predictedBy P level ref = .null := by
  by_cases hl : P level
  · simp [predictedBy, hl, h.1 hl]
  · simp [predictedBy, hl, mt h.2 hl]

theorem predictedBy_eq_lower (hl : ¬ P level) (hr : P ref) : predictedBy P level ref = .lower := by
  simp [predictedBy, hl, hr]

theorem predictedBy_self (P : Display D → Prop) [DecidablePred P] (d : Display D) :
    predictedBy P d d = .null :=
  predictedBy_eq_null Iff.rfl

variable [LinearOrder D]

/-! ### Search efficiency -/

/-- A description guides the listener's search along the most discriminable attribute it
mentions. -/
def Display.efficiency (d : Display D) : Description → D
  | .minimal => d.sufficient
  | .overinformative => max d.sufficient d.redundant

/-- The search-efficiency pressure to overinform: the redundant attribute makes the description
easier to search with. -/
def Display.Pressure (d : Display D) : Prop :=
  d.efficiency .minimal < d.efficiency .overinformative

instance (d : Display D) : Decidable d.Pressure := inferInstanceAs (Decidable (_ < _))

theorem Display.pressure_iff (d : Display D) : d.Pressure ↔ d.sufficient < d.redundant := by
  simp only [Display.Pressure, Display.efficiency, lt_max_iff, lt_self_iff_false, false_or]

/-- The rival strategy's condition for overinforming: the redundant attribute reaches the threshold
`θ` of high discriminability, whether or not it is needed. -/
def Display.HighRedundant (θ : D) (d : Display D) : Prop := θ ≤ d.redundant

instance (θ : D) (d : Display D) : Decidable (d.HighRedundant θ) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ### The display types of the first experiment -/

/-- The display types of the first experiment: the sufficient attribute of high and the redundant
one of low discriminability, the reverse, and both high. -/
inductive DisplayType
  | sHighRLow
  | sLowRHigh
  | baseline
  deriving DecidableEq, Repr

/-- The display of a type, from the low and the high calibration point. -/
def DisplayType.display (lo hi : D) : DisplayType → Display D
  | .sHighRLow => ⟨hi, lo⟩
  | .sLowRHigh => ⟨lo, hi⟩
  | .baseline => ⟨hi, hi⟩

variable {lo hi : D}

theorem pressure_sLowRHigh (h : lo < hi) : (DisplayType.sLowRHigh.display lo hi).Pressure :=
  (Display.pressure_iff _).2 h

theorem not_pressure_sHighRLow (h : lo < hi) : ¬ (DisplayType.sHighRLow.display lo hi).Pressure :=
  λ hp => absurd ((Display.pressure_iff _).1 hp) (not_lt.2 h.le)

theorem not_pressure_baseline : ¬ (DisplayType.baseline.display lo hi).Pressure :=
  λ hp => lt_irrefl _ ((Display.pressure_iff _).1 hp)

theorem predicted_sHighRLow (h : lo < hi) :
    predictedBy Display.Pressure (DisplayType.sHighRLow.display lo hi)
      (DisplayType.sLowRHigh.display lo hi) = .lower :=
  predictedBy_eq_lower (not_pressure_sHighRLow h) (pressure_sLowRHigh h)

theorem predicted_baseline (h : lo < hi) :
    predictedBy Display.Pressure (DisplayType.baseline.display lo hi)
      (DisplayType.sLowRHigh.display lo hi) = .lower :=
  predictedBy_eq_lower not_pressure_baseline (pressure_sLowRHigh h)

theorem highRedundant_predicted_baseline :
    predictedBy (Display.HighRedundant hi) (DisplayType.baseline.display lo hi)
      (DisplayType.sLowRHigh.display lo hi) = .null :=
  predictedBy_eq_null Iff.rfl

/-! ### The regressions -/

/-- The calibration points the adaptive staircases deliver for each participant and attribute: a
stimulus the participant categorizes consistently and one at the participant's category
boundary. -/
inductive Discriminability
  | low
  | high
  deriving DecidableEq, Repr

instance : LinearOrder Discriminability :=
  LinearOrder.lift' (λ d => decide (d = .high)) (by intro a b h; cases a <;> cases b <;> simp_all)

theorem Discriminability.low_lt_high : Discriminability.low < .high := by decide

/-- The predictors of the two regressions. -/
inductive Predictor
  | displayType
  | attribute
  | frequency
  deriving DecidableEq, Repr

/-- A non-reference level of a predictor: the displays of the level and of the reference level, and
the 95% credible interval of its coefficient in hundredths of a logit. -/
structure Row where
  experiment : ℕ
  predictor : Predictor
  level : Display Discriminability
  reference : Display Discriminability
  ci : ℤ × ℤ
  deriving DecidableEq

def discriminability : List (String × Discriminability) := [("low", .low), ("high", .high)]

def Row.ofDatum (ex : Datum) : Option Row := do
  let experiment ← ex.nat? "experiment"
  let predictor ← ex.parse? "predictor"
    [("displayType", .displayType), ("attribute", .attribute), ("frequency", .frequency)]
  let s ← ex.parse? "sufficient" discriminability
  let r ← ex.parse? "redundant" discriminability
  let s' ← ex.parse? "refSufficient" discriminability
  let r' ← ex.parse? "refRedundant" discriminability
  let lo ← ex.int? "ciLower"
  let hi ← ex.int? "ciUpper"
  pure ⟨experiment, predictor, ⟨s, r⟩, ⟨s', r'⟩, (lo, hi)⟩

/-- The observed direction of a level against its reference: the side of zero its credible
interval lies on, null when the interval includes zero. -/
def Row.observed (r : Row) : Direction :=
  if r.ci.2 < 0 then .lower else if 0 < r.ci.1 then .higher else .null

/-- The direction the search-efficiency view predicts for the level. -/
def Row.predicted (r : Row) : Direction := predictedBy Display.Pressure r.level r.reference

/-- The five coefficients of Tables 1 and 2. -/
def rows : List Row := Examples.all.filterMap Row.ofDatum

theorem rows_displayType_predicted :
    ∀ r ∈ rows, r.predictor = .displayType → r.observed = r.predicted := by decide

theorem rows_baseline_refutes_highRedundant :
    ∀ r ∈ rows, r.predictor = .displayType → r.level = DisplayType.baseline.display .low .high →
      r.observed ≠ predictedBy (Display.HighRedundant .high) r.level r.reference := by decide

theorem rows_attribute_level_eq_reference :
    ∀ r ∈ rows, r.predictor = .attribute → r.level = r.reference := by decide

theorem rows_attribute_observed_lower :
    ∀ r ∈ rows, r.predictor = .attribute → r.observed = .lower := by decide

theorem rows_colour_special (P : Display Discriminability → Prop) [DecidablePred P] :
    ∀ r ∈ rows, r.predictor = .attribute →
      predictedBy P r.level r.reference = .null ∧ r.observed = .lower := λ r hr hp =>
  ⟨by rw [← rows_attribute_level_eq_reference r hr hp]; exact predictedBy_self P r.level,
    rows_attribute_observed_lower r hr hp⟩

theorem rows_frequency_predicted :
    ∀ r ∈ rows, r.predictor = .frequency → r.observed = r.predicted := by decide

end GilesEtAl2026
