module

public import Studies.Krifka2007b
public import Linglib.Fragments.English.Adjectives
public import Linglib.Data.Examples.AlexandropoulouGotzner2024a

/-!
# Alexandropoulou and Gotzner (2024a): relative and absolute adjectives under negation

Two rating experiments set Horn's face-based account of negative strengthening
against Krifka's complexity-based one on three kinds of negated antonym pairs:
weak relative (*not large* vs *not small*), weak absolute (*not clean* vs *not
dirty*) and strong (*not gigantic* vs *not tiny*, *not pristine* vs *not
filthy*). The accounts' applicability conditions differ — Horn needs a semantic
extension gap, Krifka's M-principle needs semantically equivalent competitors —
so the three cases pull them apart (the paper's Table 1).

The predictions are computed from the mechanisms over the four surface forms:
Horn's R-strengthening of the face-threatening negated positive and Q/R
middling of the double negative (`hornRanges`), Krifka's BiOT quadruplet from
`Krifka2007b` (`krifkaRanges`), and its NACH extension as a comparison of
complexity deviations (`deviation`). The design's factors and the gap condition
are read off the Fragment: strength from the extreme standards of *gigantic* and
*pristine*, adjective type from the scale, and the gap from the standards. The
reported findings — an asymmetry for
weak relatives only — confirm Horn on the weak cases, refute both Krifka
variants, and leave Horn's strong-adjective prediction unsupported.

## References

* [alexandropoulou-gotzner-2024a]
* [horn-1989]
* [krifka-2007b]
* [ruytenbeek-etal-2017]
-/

@[expose] public section

namespace AlexandropoulouGotzner2024a

open Degree Krifka2007b English.Adjectives

/-! ### Design cells -/

/-- A design cell pairs an adjective type with an informational strength; Table 1 pools the two
strong cells. -/
inductive Cell
  | weakRelative
  | weakAbsolute
  | strongRelative
  | strongAbsolute
  deriving DecidableEq, Fintype

/-- `c.pair` is the cell's antonym pair, whose positive pole is the evaluatively positive
member. -/
def Cell.pair : Cell → AntonymPair
  | .weakRelative   => size
  | .weakAbsolute   => cleanliness
  | .strongRelative => extremeSize
  | .strongAbsolute => pristineness

/-- A cell is strong when its adjectives are extreme, with standards beyond the weak pair's. -/
def Cell.IsStrong (c : Cell) : Prop := c.pair.pos.standard = .extreme

instance : DecidablePred Cell.IsStrong :=
  fun c ↦ inferInstanceAs (Decidable (c.pair.pos.standard = .extreme))

/-- A cell is relative when its scale is, an open scale with no endpoint to fix a standard. -/
def Cell.IsRelative (c : Cell) : Prop := c.pair.pos.boundedness.IsRelative

instance : DecidablePred Cell.IsRelative :=
  fun c ↦ inferInstanceAs (Decidable c.pair.pos.boundedness.IsRelative)

/-- The pair leaves a semantic extension gap when its poles do not take complementary standards. -/
def Cell.HasGap (c : Cell) : Prop := ¬ c.pair.ComplementaryStandards

instance : DecidablePred Cell.HasGap :=
  fun c ↦ inferInstanceAs (Decidable (¬ c.pair.ComplementaryStandards))

theorem isStrong_iff (c : Cell) : c.IsStrong ↔ c = .strongRelative ∨ c = .strongAbsolute := by
  cases c <;> decide

theorem isRelative_iff (c : Cell) : c.IsRelative ↔ c = .weakRelative ∨ c = .strongRelative := by
  cases c <;> decide

theorem hasGap_iff (c : Cell) : c.HasGap ↔ c ≠ .weakAbsolute := by
  cases c <;> decide

/-! ### Communicated ranges -/

/-- A `Ranges` assigns each surface form the scale regions it may communicate. -/
abbrev Ranges := AntonymForm → Finset Region

/-- A negated antonym pair is interpreted asymmetrically when the negated positive and the negated
negative forms diverge, and symmetrically when they behave in parallel. -/
inductive Asymmetry where
  | asymmetric
  | symmetric
  deriving Repr, DecidableEq, Fintype

/-- Positive and negative forms communicate mirror-image ranges. -/
def Ranges.Symmetric (r : Ranges) : Prop := ∀ f, r f.flip = (r f).image Region.flip

instance (r : Ranges) : Decidable r.Symmetric := Fintype.decidableForallFintype

def Ranges.asymmetry (r : Ranges) : Asymmetry :=
  if r.Symmetric then .symmetric else .asymmetric

/-- Horn's ranges assume a semantic gap. The negated positive is R-strengthened to the
    face-threatening antonym it conceals, while the prolix double negative is Q/R-restricted to the
    gap the simpler positive could not describe. -/
def hornRanges : Ranges
  | .positive    => {.positive}
  | .negative    => {.negative}
  | .notPositive => {.negative}
  | .notNegative => {.plateauLow, .plateauHigh}

/-- Krifka's ranges are the BiOT quadruplet of `Krifka2007b`. -/
def krifkaRanges : Ranges := fun f ↦ (krifkaQuadruplet.filter (·.1 = f)).image (·.2)

theorem hornRanges_asymmetric : hornRanges.asymmetry = .asymmetric := by decide

theorem krifkaRanges_symmetric : krifkaRanges.asymmetry = .symmetric := by decide

/-! ### The Negative Adjectives Complexity Hypothesis -/

/-- `complexity nach f` is the complexity of the form `f` with (`true`) or without (`false`)
    NACH. Under NACH the negative
    adjective carries a covert negative morpheme, so *small* counts like *unhappy*;
    without it the simple antonyms are equally simple and their negations equally
    complex. -/
def complexity : Bool → AntonymForm → ℕ
  | true, f => f.complexity
  | false, .positive | false, .negative => 0
  | false, .notPositive | false, .notNegative => 3

/-- `simpleOf f` is the simple form co-extensive with `f` under bivalent semantics. -/
def simpleOf : AntonymForm → AntonymForm
  | .notPositive => .negative
  | .notNegative => .positive
  | f => f

/-- `deviation nach f` is the excess complexity of `f` over its co-extensive simple form, the
    stereotype deviation the M-principle assigns it. -/
def deviation (nach : Bool) (f : AntonymForm) : ℕ :=
  complexity nach f - complexity nach (simpleOf f)

theorem deviation_nach :
    deviation false .notPositive = deviation false .notNegative ∧
    deviation true .notPositive < deviation true .notNegative := by
  decide

/-! ### Table 1 -/

/-- `horn c` is Horn's prediction for a cell, made where a semantic gap makes the account
applicable. -/
def horn (c : Cell) : Option Asymmetry :=
  if c.HasGap then some hornRanges.asymmetry else none

/-- Krifka's account, with or without NACH, makes a prediction only for weak pairs, since the
    M-principle needs semantically equivalent competitors, which only weak pairs provide (by
    bivalence for relatives, by entailment for absolutes). -/
def krifka (nach : Bool) (c : Cell) : Option Asymmetry :=
  if c.IsStrong then none
  else some (if deviation nach .notPositive = deviation nach .notNegative then .symmetric
    else .asymmetric)

theorem table1_weakRelative :
    horn .weakRelative = some .asymmetric ∧ krifka false .weakRelative = some .symmetric ∧
    krifka true .weakRelative = some .asymmetric := by
  decide

theorem table1_weakAbsolute :
    horn .weakAbsolute = none ∧ krifka false .weakAbsolute = some .symmetric ∧
    krifka true .weakAbsolute = some .asymmetric := by
  decide

theorem table1_strong :
    ∀ c : Cell, c.IsStrong →
      horn c = some .asymmetric ∧ krifka false c = none ∧ krifka true c = none := by
  decide

/-! ### Findings -/

/-- `finding c` is the reported interpretation pattern of a cell. Experiment 1 found a Negation
    effect for weak relatives (β = 0.64, p < .01) and none with strong as the reference level
    (p = 0.86); Experiment 2 found none for weak absolutes (p = 0.17) and only a marginal one for
    strong absolutes (p = 0.07). -/
def finding : Cell → Asymmetry
  | .weakRelative => .asymmetric
  | _ => .symmetric

theorem horn_confirmed_on_weak :
    ∀ c : Cell, ¬ c.IsStrong → ∀ p ∈ horn c, p = finding c := by
  decide

theorem horn_unsupported_on_strong :
    ∀ c : Cell, c.IsStrong → horn c ≠ some (finding c) := by
  decide

theorem krifka_refuted :
    krifka false .weakRelative ≠ some (finding .weakRelative) ∧
    krifka true .weakAbsolute ≠ some (finding .weakAbsolute) := by
  decide

theorem gap_precondition : ∀ c : Cell, finding c = .asymmetric → c.HasGap := by
  decide

/-! ### Rows -/

/-- `entryOf a` is the Fragment entry for the adjective `a` of the size and cleanliness
items. -/
def entryOf : String → Option GradableAdjective
  | "large" => some large | "small" => some small
  | "gigantic" => some gigantic | "tiny" => some tiny
  | "clean" => some clean | "dirty" => some dirty
  | "pristine" => some pristine | "filthy" => some filthy
  | _ => none

/-- `formOf row` is the surface form of a statement row, read off its polarity and negation
conditions. -/
def formOf (row : Datum) : Option AntonymForm :=
  match row.feature? "polarity", row.feature? "negation" with
  | some "positive", some "nonNegated" => some .positive
  | some "positive", some "negated" => some .notPositive
  | some "negative", some "nonNegated" => some .negative
  | some "negative", some "negated" => some .notNegative
  | _, _ => none

theorem row_factors :
    ∀ row ∈ Examples.all, ∀ a ∈ (row.feature? "adjective").bind entryOf,
      (row.feature? "strength" = some "strong" ↔ a.standard = .extreme) ∧
        (row.feature? "adjectiveType" = some "relative" ↔ a.boundedness.IsRelative) := by
  decide

theorem negated_iff_not :
    ∀ row ∈ Examples.all, ∀ n ∈ row.feature? "negation",
      (n = "negated" ↔ " not ".toList <:+: row.primaryText.toList) := by
  decide

end AlexandropoulouGotzner2024a
