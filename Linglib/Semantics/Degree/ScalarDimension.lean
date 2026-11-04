module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Semantics.Degree.PositiveStandard
public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.Quantity.Dimension

/-!
# Scalar dimensions

`ScalarDimension` lists the dimensions along which gradable adjectives and degree achievements
measure, such as height, temperature and fullness. A dimension has the shape of its scale and, when
it is a dimension of physical measurement, the physical dimension its degrees are measured in.
Evaluative and psychological scales have none, which is why they reject measure phrases (*six feet
tall* but not *six feet happy*). The degrees of a dimension are the canonical linear order of its
scale's shape, and [a degree achievement is telic by default exactly when they have a greatest
element](##ScalarDimension.defaultTelicity_telic_iff_hasGreatest).

## Implementation notes

Speed is a primitive lexical scale although physically a quotient, in line with Bale and Schwarz's
hypothesis that semantic composition has no quantity division. Degrees are the integers with the
endpoints of the scale adjoined (`Boundedness.DegreeShape`), where Kennedy and McNally take the
reals between 0 and 1; nothing here or in `Semantics/Degree/PositiveStandard.lean` depends on
density, which Fox and Hackl's Universal Density of Measurement asserts of every scale.

## References

* [cresswell-1976]
* [kennedy-mcnally-2005]
* [kennedy-2007]
* [kennedy-levin-2008]
* [lassiter-2017]
* [bale-schwarz-2026]
* [fox-hackl-2006]
-/

@[expose] public section

open Aspect

/-- A scalar dimension is what a gradable adjective or a degree achievement measures along. -/
inductive ScalarDimension
  -- Size
  | height | width | length | weight | thickness | depth | speed | strength
  | age | generalSize
  -- Sensory
  | temperature | brightness | volume | taste
  -- Evaluative
  | happiness | cost | price | quality | value | danger | beauty | importance | safety | tragedy
  -- Psychological
  | intelligence | wisdom | expectation | possibility | confidence
  -- State (adjective + deadjectival-verb change dimensions)
  | fullness | wetness | cleanliness | straightness | flatness | openness
  | freedom | tightness | alive | pregnancy | hardness | smoothness | purity
  | cracking | denting | scratching | shattering
  -- Perceptual colour + verb-only scalar-change dimensions
  | color | boiling | corrosion | quantity | unspecified
  deriving DecidableEq, Repr, Fintype, Inhabited, BEq

/-- The shape of a dimension's scale in its increasing direction ([kennedy-mcnally-2005]
    (24)–(27), [kennedy-2007] (33), (49)–(50), (60)). Wetness is lower closed, *wet* taking a
    minimum standard and *dry* a maximum one, straightness upper closed, by *fully straight*
    against *??fully bent*, and fullness closed, by *100% full* and *100% empty*. Possibility is
    lower closed, since nothing is less possible than the impossible ([lassiter-2017] §5.2.3), so
    *possible* takes a minimum standard and *impossible* a maximum one, as *wet* and *dry* do;
    whether it also has a maximum turns on the disputed identity of its scale with that of
    *likely*. The negative member of an antonym pair measures on the dual scale. The definition is
    reducible, so that order instances on the degrees of a dimension see through it. -/
abbrev ScalarDimension.boundedness : ScalarDimension → Boundedness
  | .openness | .cracking | .denting | .scratching | .boiling
  | .alive | .freedom | .fullness | .shattering | .tightness | .pregnancy => .closed
  | .straightness | .flatness | .cleanliness | .purity | .smoothness | .safety
  | .confidence => .upperClosed
  | .wetness | .possibility => .lowerClosed
  | .height | .width | .length | .weight | .thickness | .depth | .speed
  | .strength | .age | .generalSize | .temperature | .brightness | .volume | .taste
  | .happiness | .cost | .price | .quality | .value | .danger | .beauty | .tragedy
  | .importance | .intelligence | .wisdom | .expectation
  | .hardness | .color | .corrosion | .quantity
  | .unspecified => .open_

/-! ### Bridges to the physical quantity algebra -/

/-- The physical dimension a scalar dimension is measured in, if any. Spatial scales are
    measured in length, weight in mass, age in time and temperature in thermodynamic temperature;
    quantity counts, so it has dimension `1`; and *fast* lexicalizes speed, the quotient of length
    by time, as a primitive scale. Evaluative, psychological and state scales, which reject ratio
    measure phrases, have none. -/
def ScalarDimension.dimension? : ScalarDimension → Option QuantityDimension
  | .height | .width | .length | .depth | .thickness => some (.of .length)
  | .weight => some (.of .mass)
  | .age => some (.of .time)
  | .temperature => some (.of .thermodynamicTemperature)
  | .quantity => some 1
  | .speed => some .speed
  | _ => none

/-- A comparison scale is what two adjectives must share to be compared: a physical dimension, or
for an adjective without one its own dimension. -/
abbrev ComparisonScale := QuantityDimension ⊕ ScalarDimension

/-- The comparison scale of a dimension is its physical dimension where it has one, so *tall* and
*wide* share a scale of linear extent, and otherwise the dimension itself, as *clever* induces its
own scale of cleverness in [cresswell-1976] (2.4). -/
def ScalarDimension.comparisonScale (d : ScalarDimension) : ComparisonScale :=
  d.dimension?.elim (.inr d) .inl

/-! ### Degrees -/

/-- The degrees of a dimension are the canonical linear order of its scale's shape. -/
abbrev ScalarDimension.Scale (d : ScalarDimension) : Type := d.boundedness.DegreeShape
instance instLinearOrderScale (d : ScalarDimension) : LinearOrder d.Scale :=
  inferInstance

theorem ScalarDimension.hasGreatest_scale_iff (d : ScalarDimension) :
    (∃ m : d.Scale, IsTop m) ↔ d.boundedness.HasMax :=
  Boundedness.exists_isTop_degreeShape d.boundedness

/-! ### Degree achievements -/

/-- A degree achievement on a scale of shape `b` is by default an accomplishment when Interpretive
    Economy prefers the maximum standard on `b` with a least degree adjoined, the scale of its
    measure of change, and an activity otherwise ([kennedy-levin-2008]). -/
def Boundedness.defaultVendlerClass (b : Boundedness) : VendlerClass :=
  if b.withMin.defaultStandard = .maxEndpoint then .accomplishment else .activity

theorem Boundedness.defaultVendlerClass_eq_accomplishment_iff {b : Boundedness} :
    b.defaultVendlerClass = .accomplishment ↔ b.HasMax := by
  cases b <;> decide

theorem Boundedness.telicity_defaultVendlerClass_eq_telic_iff {b : Boundedness} :
    b.defaultVendlerClass.telicity = .telic ↔ b.HasMax := by
  cases b <;> decide

/-- The default Vendler class of a degree achievement towards the positive pole of a dimension is
    that of the dimension's scale. -/
def ScalarDimension.defaultVendlerClass (d : ScalarDimension) : VendlerClass :=
  d.boundedness.defaultVendlerClass

/-- The default telicity of a degree achievement on a dimension is that of its default Vendler
    class. -/
def ScalarDimension.defaultTelicity (d : ScalarDimension) : Telicity :=
  d.defaultVendlerClass.telicity

/-- A degree achievement is telic by default exactly when the degrees of its scale have a
    greatest element ([kennedy-levin-2008]). -/
theorem ScalarDimension.defaultTelicity_telic_iff_hasGreatest (d : ScalarDimension) :
    d.defaultTelicity = .telic ↔ ∃ m : d.Scale, IsTop m :=
  Boundedness.telicity_defaultVendlerClass_eq_telic_iff.trans
    (ScalarDimension.hasGreatest_scale_iff d).symm

@[simp] theorem ScalarDimension.telicity_defaultVendlerClass (d : ScalarDimension) :
    d.defaultVendlerClass.telicity = d.defaultTelicity := rfl

@[simp] theorem ScalarDimension.duration_defaultVendlerClass (d : ScalarDimension) :
    d.defaultVendlerClass.duration = .durative := by
  unfold defaultVendlerClass Boundedness.defaultVendlerClass; cases d.boundedness <;> rfl

@[simp] theorem ScalarDimension.dynamicity_defaultVendlerClass (d : ScalarDimension) :
    d.defaultVendlerClass.dynamicity = .dynamic := by
  unfold defaultVendlerClass Boundedness.defaultVendlerClass; cases d.boundedness <;> rfl

