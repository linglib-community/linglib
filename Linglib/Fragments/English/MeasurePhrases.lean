module

public import Linglib.Semantics.Degree.Measure.Quantity
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Pow

/-!
# English measure phrases

The English nouns that quantize a mass noun in a pseudo-partitive (*three grams of salt*,
*three glasses of water*, *three grains of rice*) are measure terms, which name a unit quantity
of a dimension, and the container nouns and atomizers of Scontras's classification. A measure
term carries the size of its unit in the coherent unit of its dimension, so that a kilogram is a
thousand grams (`kilogram_quantity`) and a cubic meter a thousand liters
(`meter_quantity_pow_three`).

## Implementation notes

* The reference units are the coherent CGS units, the gram, the centimeter, the second and their
  products, so that a milliliter, a cubic centimeter, has size `1`. Quantities multiply
  componentwise only because the units are coherent.
* A unit's size is a convention, and the conventions are exact rationals: the SI prefixes are
  powers of ten, and the pound and the mile are exact decimals of the kilogram and the meter. The
  fragment stores them in `ℚ`, and a measure term denotes a quantity with real magnitude.

## References

* [scontras-2014]
* [bale-schwarz-2022]
* [bipm-2019]
-/

@[expose] public section

namespace English.MeasurePhrases

open Degree (QuantityDimension QuantizingNounClass)

/-- A measure term, a noun naming a unit quantity of a dimension. -/
structure MeasureTerm where
  form : String
  formPlural : String
  /-- The unit's symbol in the quantity calculus (`g`, `mL`, `km`). -/
  symbol : String
  dimension : QuantityDimension
  /-- The size of the unit in the coherent CGS unit of its dimension; a kilogram is `1000` grams
  and a meter `100` centimeters. -/
  magnitude : ℚ := 1
  magnitude_pos : 0 < magnitude := by decide +kernel
  deriving Repr

namespace MeasureTerm

open Degree

/-- The unit quantity a measure term denotes, its size in the reference unit times the unit
quantity of its dimension. -/
def quantity (t : MeasureTerm) : Quantity ℝ := ((t.magnitude : ℝ), t.dimension)

variable {t t' : MeasureTerm} {k : ℝ}

@[simp] theorem quantity_fst (t : MeasureTerm) : t.quantity.1 = t.magnitude := rfl

@[simp] theorem quantity_snd (t : MeasureTerm) : t.quantity.2 = t.dimension := rfl

/-- A unit has positive size. -/
theorem cast_magnitude_pos (t : MeasureTerm) : (0 : ℝ) < t.magnitude :=
  Rat.cast_pos.mpr t.magnitude_pos

/-- One unit is `k` of another when its size is `k` times the other's in their common
dimension. -/
theorem quantity_eq_pure_mul_iff :
    t'.quantity = .pure k * t.quantity ↔
      (t'.magnitude : ℝ) = k * t.magnitude ∧ t'.dimension = t.dimension := by
  simp [Prod.ext_iff]

end MeasureTerm

/-- *gram*. -/
def gram : MeasureTerm :=
  { form := "gram", formPlural := "grams", symbol := "g", dimension := .of .mass }
/-- *kilogram*. -/
def kilogram : MeasureTerm :=
  { form := "kilogram", formPlural := "kilograms", symbol := "kg", dimension := .of .mass,
    magnitude := 1000 }
/-- *kilo*. -/
def kilo : MeasureTerm :=
  { form := "kilo", formPlural := "kilos", symbol := "kg", dimension := .of .mass,
    magnitude := 1000 }
/-- *pound*. -/
def pound : MeasureTerm :=
  { form := "pound", formPlural := "pounds", symbol := "lb", dimension := .of .mass,
    magnitude := 45359237 / 100000 }
/-- *milliliter*. -/
def milliliter : MeasureTerm :=
  { form := "milliliter", formPlural := "milliliters", symbol := "mL",
    dimension := .volume }
/-- *liter*. -/
def liter : MeasureTerm :=
  { form := "liter", formPlural := "liters", symbol := "L", dimension := .volume,
    magnitude := 1000 }
/-- *mile*. -/
def mile : MeasureTerm :=
  { form := "mile", formPlural := "miles", symbol := "mi", dimension := .of .length,
    magnitude := 1609344 / 10 }
/-- *kilometer*. -/
def kilometer : MeasureTerm :=
  { form := "kilometer", formPlural := "kilometers", symbol := "km", dimension := .of .length,
    magnitude := 100000 }
/-- *meter*. -/
def meter : MeasureTerm :=
  { form := "meter", formPlural := "meters", symbol := "m", dimension := .of .length,
    magnitude := 100 }
/-- *hour*. -/
def hour : MeasureTerm :=
  { form := "hour", formPlural := "hours", symbol := "h", dimension := .of .time,
    magnitude := 3600 }
/-- *second*. -/
def second_ : MeasureTerm :=
  { form := "second", formPlural := "seconds", symbol := "s", dimension := .of .time }

/-- A kilogram is a thousand grams. -/
theorem kilogram_quantity : kilogram.quantity = .pure 1000 * gram.quantity := by
  simp [MeasureTerm.quantity_eq_pure_mul_iff, kilogram, gram]

/-- A liter is a thousand milliliters. -/
theorem liter_quantity : liter.quantity = .pure 1000 * milliliter.quantity := by
  simp [MeasureTerm.quantity_eq_pure_mul_iff, liter, milliliter]

/-- A cubic meter is a thousand liters. -/
theorem meter_quantity_pow_three : meter.quantity ^ 3 = .pure 1000 * liter.quantity := by
  ext
  · norm_num [MeasureTerm.quantity, meter, liter]
  · simp [MeasureTerm.quantity, meter, liter, QuantityDimension.volume]

/-- The measure terms. -/
def allMeasureTerms : List MeasureTerm :=
  [gram, kilogram, kilo, pound, milliliter, liter, mile, kilometer, meter, hour, second_]

/-- The measure term with singular or plural form `s`. -/
def measureTerm? (s : String) : Option MeasureTerm :=
  allMeasureTerms.find? fun t ↦ t.form = s ∨ t.formPlural = s

/-- A quantizing noun turns a mass term into a countable expression, as a measure term, a
container noun or an atomizer. -/
structure QuantizingNoun where
  form : String
  formPlural : String
  nounClass : QuantizingNounClass
  /-- The dimension a measure term names, or that a container noun measures on its
  measure reading; atomizers name no measure function. -/
  dimension : Option QuantityDimension := none
  deriving Repr, BEq

/-- A measure term as a quantizing noun. -/
def MeasureTerm.toQuantizingNoun (t : MeasureTerm) : QuantizingNoun :=
  { form := t.form, formPlural := t.formPlural, nounClass := .measureTerm,
    dimension := some t.dimension }

instance : Coe MeasureTerm QuantizingNoun := ⟨MeasureTerm.toQuantizingNoun⟩

/-- *glass*. -/
def glass : QuantizingNoun :=
  { form := "glass", formPlural := "glasses", nounClass := .containerNoun,
    dimension := some .volume }
/-- *box*. -/
def box : QuantizingNoun :=
  { form := "box", formPlural := "boxes", nounClass := .containerNoun, dimension := some .volume }
/-- *cup*. -/
def cup : QuantizingNoun :=
  { form := "cup", formPlural := "cups", nounClass := .containerNoun, dimension := some .volume }
/-- *bag*. -/
def bag : QuantizingNoun :=
  { form := "bag", formPlural := "bags", nounClass := .containerNoun, dimension := some .volume }
/-- *bottle*. -/
def bottle : QuantizingNoun :=
  { form := "bottle", formPlural := "bottles", nounClass := .containerNoun,
    dimension := some .volume }
/-- *grain*. -/
def grain : QuantizingNoun :=
  { form := "grain", formPlural := "grains", nounClass := .atomizer }
/-- *piece*. -/
def piece : QuantizingNoun :=
  { form := "piece", formPlural := "pieces", nounClass := .atomizer }
/-- *drop*. -/
def drop : QuantizingNoun :=
  { form := "drop", formPlural := "drops", nounClass := .atomizer }
/-- *slice*. -/
def slice : QuantizingNoun :=
  { form := "slice", formPlural := "slices", nounClass := .atomizer }
/-- *chunk*. -/
def chunk : QuantizingNoun :=
  { form := "chunk", formPlural := "chunks", nounClass := .atomizer }

/-- The quantizing nouns. -/
def allQuantizingNouns : List QuantizingNoun :=
  allMeasureTerms.map (↑) ++ [glass, box, cup, bag, bottle, grain, piece, drop, slice, chunk]

end English.MeasurePhrases
