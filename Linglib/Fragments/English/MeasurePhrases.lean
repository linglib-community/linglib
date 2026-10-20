module

public import Linglib.Semantics.Degree.Measure.Quantity
public import Linglib.Fragments.English.Nouns
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# English measure phrases

The English nouns that quantize a mass noun in a pseudo-partitive (*three grams of salt*,
*three glasses of water*, *three grains of rice*) are measure terms, which name a unit quantity
of a dimension, container nouns and atomizers. A measure term carries the size of its unit in the
coherent unit of its dimension, so that a kilogram is a thousand grams (`kilogram_quantity`), a
cubic meter a thousand liters (`meter_quantity_pow_three`), and a psi the weight of a pound under
standard gravity spread over a square inch (`psi_quantity`). Container nouns and atomizers are
plain count nouns, listed in `containerNouns` and `atomizers`.

## Main definitions

* `MeasureTerm`: a count noun naming a unit quantity, with `MeasureTerm.quantity`.
* `measureTerms`, `containerNouns`, `atomizers`: the three inventories.

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
* [bale-schwarz-2026]
* [bipm-2019]
-/

@[expose] public section

namespace English.MeasurePhrases

open Degree (QuantityDimension Quantity)

/-- A measure term, a count noun naming a unit quantity of a dimension. -/
structure MeasureTerm extends toEnglishNoun : Nouns.Noun where
  /-- The unit's symbol in the quantity calculus (`g`, `mL`, `km`). -/
  symbol : String
  /-- The dimension of the unit. -/
  dimension : QuantityDimension
  /-- The size of the unit in the coherent CGS unit of its dimension; a kilogram is `1000` grams
  and a meter `100` centimeters. -/
  magnitude : ℚ := 1
  magnitude_pos : 0 < magnitude := by decide +kernel

namespace MeasureTerm

/-- The unit quantity a measure term denotes, its size in the reference unit times the unit
quantity of its dimension. -/
def quantity (t : MeasureTerm) : Quantity ℝ := ((t.magnitude : ℝ), t.dimension)

variable {t t' : MeasureTerm} {k : ℝ}

@[simp] theorem quantity_fst (t : MeasureTerm) : t.quantity.1 = t.magnitude := rfl

@[simp] theorem quantity_snd (t : MeasureTerm) : t.quantity.2 = t.dimension := rfl

/-- A unit has positive size. -/
theorem cast_magnitude_pos (t : MeasureTerm) : (0 : ℝ) < t.magnitude :=
  Rat.cast_pos.mpr t.magnitude_pos

/-- A unit quantity is invertible. -/
theorem isUnit_quantity (t : MeasureTerm) : IsUnit t.quantity :=
  Quantity.isUnit_iff.2 t.cast_magnitude_pos.ne'

/-- One unit is `k` of another when its size is `k` times the other's in their common
dimension. -/
theorem quantity_eq_pure_mul_iff :
    t'.quantity = .pure k * t.quantity ↔
      (t'.magnitude : ℝ) = k * t.magnitude ∧ t'.dimension = t.dimension := by
  simp [Prod.ext_iff]

end MeasureTerm

/-! ### Measure terms -/

/-- *gram*. -/
def gram : MeasureTerm := { Nouns.Noun.common "gram" with symbol := "g", dimension := .of .mass }
/-- *kilogram*. -/
def kilogram : MeasureTerm :=
  { Nouns.Noun.common "kilogram" with symbol := "kg", dimension := .of .mass, magnitude := 1000 }
/-- *kilo*, a clipping of *kilogram*, which takes the plural *kilos*. -/
def kilo : MeasureTerm :=
  { Nouns.Noun.common "kilo" with
    plural := some "kilos", symbol := "kg", dimension := .of .mass, magnitude := 1000 }
/-- *pound*. -/
def pound : MeasureTerm :=
  { Nouns.Noun.common "pound" with
    symbol := "lb", dimension := .of .mass, magnitude := 45359237 / 100000 }
/-- *milliliter*. -/
def milliliter : MeasureTerm :=
  { Nouns.Noun.common "milliliter" with symbol := "mL", dimension := .volume }
/-- *liter*. -/
def liter : MeasureTerm :=
  { Nouns.Noun.common "liter" with symbol := "L", dimension := .volume, magnitude := 1000 }
/-- *inch*. -/
def inch : MeasureTerm :=
  { Nouns.Noun.common "inch" with symbol := "in", dimension := .of .length, magnitude := 254 / 100 }
/-- *mile*. -/
def mile : MeasureTerm :=
  { Nouns.Noun.common "mile" with
    symbol := "mi", dimension := .of .length, magnitude := 1609344 / 10 }
/-- *kilometer*. -/
def kilometer : MeasureTerm :=
  { Nouns.Noun.common "kilometer" with
    symbol := "km", dimension := .of .length, magnitude := 100000 }
/-- *meter*. -/
def meter : MeasureTerm :=
  { Nouns.Noun.common "meter" with symbol := "m", dimension := .of .length, magnitude := 100 }
/-- *hour*. -/
def hour : MeasureTerm :=
  { Nouns.Noun.common "hour" with symbol := "h", dimension := .of .time, magnitude := 3600 }
/-- *second*. -/
def second : MeasureTerm :=
  { Nouns.Noun.common "second" with symbol := "s", dimension := .of .time }
/-- *psi*, pound-force per square inch, a unit noun to the speakers who know it only as an
initialism ([bale-schwarz-2026]); its plural is *psi*. -/
def psi : MeasureTerm :=
  { Nouns.Noun.common "psi" with
    plural := some "psi", symbol := "psi", dimension := .pressure
    magnitude := pound.magnitude * (980665 / 1000) / inch.magnitude ^ 2 }

/-- The standard acceleration of gravity, `980.665 cm/s²` ([bipm-2019]), under which a mass of a
pound weighs a pound-force. -/
def standardGravity : Quantity ℝ := ((980665 / 1000 : ℚ), .of .length / .of .time ^ 2)

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

/-- A mile is 63360 inches. -/
theorem mile_quantity : mile.quantity = .pure 63360 * inch.quantity := by
  norm_num [MeasureTerm.quantity_eq_pure_mul_iff, mile, inch]

/-- A psi is the weight of a pound under standard gravity spread over a square inch. -/
theorem psi_quantity :
    psi.quantity = pound.quantity * standardGravity / inch.quantity ^ 2 := by
  refine Prod.ext ?_ ?_
  · norm_num [MeasureTerm.quantity, psi, pound, inch, standardGravity]
  · simp only [MeasureTerm.quantity, standardGravity, Prod.snd_div, Prod.snd_mul, Prod.pow_snd]
    decide

/-- The measure terms. -/
def measureTerms : List MeasureTerm :=
  [gram, kilogram, kilo, pound, milliliter, liter, inch, mile, kilometer, meter, hour, second,
    psi]

/-- The measure term with singular or plural form `s`. -/
def measureTerm? (s : String) : Option MeasureTerm :=
  measureTerms.find? fun t ↦ t.form = s ∨ t.plural = some s

/-! ### Container nouns and atomizers -/

/-- *glass*. -/
def glass : Nouns.Noun := .common "glass"
/-- *box*. -/
def box : Nouns.Noun := .common "box"
/-- *cup*. -/
def cup : Nouns.Noun := .common "cup"
/-- *bag*. -/
def bag : Nouns.Noun := .common "bag"
/-- *bottle*. -/
def bottle : Nouns.Noun := .common "bottle"
/-- *bucket*. -/
def bucket : Nouns.Noun := .common "bucket"
/-- *grain*. -/
def grain : Nouns.Noun := .common "grain"
/-- *piece*. -/
def piece : Nouns.Noun := .common "piece"
/-- *drop*. -/
def drop : Nouns.Noun := .common "drop"
/-- *slice*. -/
def slice : Nouns.Noun := .common "slice"
/-- *chunk*. -/
def chunk : Nouns.Noun := .common "chunk"
/-- *quantity*. -/
def quantity : Nouns.Noun := .common "quantity"

/-- The container nouns, count nouns of containers that measure by their capacity on a measure
reading, as in *three glasses of water*. -/
def containerNouns : List Nouns.Noun := [glass, box, cup, bag, bottle, bucket]

/-- The atomizers, count nouns that partition a substance into countable units, as in *three
grains of rice*. -/
def atomizers : List Nouns.Noun := [grain, piece, drop, slice, chunk, quantity]

end English.MeasurePhrases
