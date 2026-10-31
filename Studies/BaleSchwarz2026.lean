module

public import Studies.BaleSchwarz2022
public import Linglib.Data.Examples.BaleSchwarz2026
public import Linglib.Data.Examples.Readers

/-!
# Bale and Schwarz (2026): Natural language and external conventions: re-examining per

*Per*-phrases come in two kinds. Saturating a predicate of a simplex dimension, as in *this
sample weighs thirteen grams per milliliter*, they compose in the grammar, and both Coppock's
entry for *per* and the anaphoric entry of the 2022 paper can be restated with pure numbers and
multiplication alone, so neither commits the grammar to the quantity division that the No Division
Hypothesis denies it. Saturating a predicate of a quotient dimension, as in *the density of that
sample is thirteen grams per milliliter*, they are math speak, verbalizations of the term
`13 g/mL` whose meaning comes from the external notation as a mixed quotation's does. A
verbalization such as *thirteen gee over em el* substitutes only for math speak, and
only a composed *per*-PP can be fronted. Both facts reduce to dimensions: a composed
*per*-phrase has its head unit's dimension, so it can be a weight but never a density, while
`13 g/mL` is a density and never a weight.

## TODO

`rows_dimension` passes over five rows. *Pounds per square inch* in (22) is an idiom for *psi*
over the pound-force, not the pound of the fragment; (25b) and (26b) verbalize the symbol `mph`;
and (3) and (24) name no predicate dimension.

## References

* [bale-schwarz-2026]
* [bale-schwarz-2022]
* [coppock-2021]
* [coppock-2022]
* [davidson-1979]
-/

@[expose] public section

namespace BaleSchwarz2026

open Degree Quantity English.MeasurePhrases BaleSchwarz2022

noncomputable section

variable {E : Type*} {w : World E} {D D₁ D₂ : QuantityDimension} {x y : E} {n : ℝ}
  {u r : MeasureTerm}

/-! ### Multiplication only -/

-- (21)
theorem anaphoricPer_eq_pure_iff :
    anaphoricPer w r y = pure n ↔ pure n * r.quantity = w.quantity r.dimension y :=
  r.isUnit_quantity.div_eq_iff.trans eq_comm

/-- The pure number the anaphoric *per* denotes is the unique `n` with `n ⋅ r = μ(y)`, so the entry
needs no division. -/
theorem existsUnique_pure_mul : ∃! n : ℝ, pure n * r.quantity = w.quantity r.dimension y :=
  ⟨(anaphoricPer w r y).1, anaphoricPer_eq_pure_iff.1 (Prod.ext rfl anaphoricPer_snd),
    fun _ h ↦ congrArg Prod.fst (anaphoricPer_eq_pure_iff.2 h).symm⟩

/-- Coppock's *per* ((9), (15)) takes the measure predicate `f` as an argument,
`λq λr λf λx. max{d | f d x} = μ_dim(q)(x) / q ⋅ r`. -/
def coppockPer (w : World E) (r : MeasureTerm) (q : Quantity ℝ) (f : Quantity ℝ → E → Prop)
    (x : E) : Prop :=
  ∃ d, IsGreatest {d | f d x} d ∧ d = anaphoricPer w r x * q

/-- With the measure predicate `λd λx. μ_D(x) = d`, Coppock's entry and the anaphoric measure
phrase derive the same truth conditions ((14)). -/
theorem coppockPer_much_iff :
    coppockPer w r (pure n * u.quantity) (much (w.quantity D)) x ↔
      much (w.quantity D) (anaphoricMP w n u r x) x := by
  simp only [coppockPer, much, Set.ofPred_eq_eq_singleton', anaphoricMP,
    mul_comm _ (anaphoricPer w r x)]
  exact ⟨fun ⟨_, hd, h⟩ ↦ (hd.unique isGreatest_singleton).symm.trans h,
    fun h ↦ ⟨_, isGreatest_singleton, h⟩⟩

/-! ### Math speak -/

/-- A verbalization of the quantity-calculus term `n u / r` denotes that quotient. -/
def mathSpeak (n : ℝ) (u r : MeasureTerm) : Quantity ℝ := divisionMP n u r

/-- `ratio w D₁ D₂` is the measure `μ_{D₁} / μ_{D₂}` of a quotient dimension, such as density or
speed. -/
def ratio (w : World E) (D₁ D₂ : QuantityDimension) (x : E) : Quantity ℝ :=
  w.quantity D₁ x / w.quantity D₂ x

@[simp] theorem ratio_snd : (ratio w D₁ D₂ x).2 = D₁ / D₂ := by simp [ratio]

theorem density_eq_ratio : density w x = ratio w (.of .mass) .volume x := rfl

/-- A predicate of a quotient dimension accepts the verbalized quotient ((2), (6), (25)):
`μ_{D₁}(x) / μ_{D₂}(x) = n u / r`. -/
theorem ratio_eq_mathSpeak_iff (hu : u.dimension = D₁) (hr : r.dimension = D₂) :
    ratio w D₁ D₂ x = mathSpeak n u r ↔ w D₁ x / w D₂ x = n * u.magnitude / r.magnitude := by
  simp [ratio, mathSpeak, divisionMP, divisionPer, Prod.ext_iff, hu, hr]

/-- An anaphoric measure phrase of dimension `D₁` is never a ratio of `D₁` by another dimension, so
composed *per*-phrases are out ((27), (28)). -/
theorem ratio_ne_anaphoricMP (hu : u.dimension = D₁) (hD₂ : D₂ ≠ 1) :
    ratio w D₁ D₂ x ≠ anaphoricMP w n u r y :=
  fun h ↦ hD₂ <| by simpa [hu] using congrArg Prod.snd h

/-- A predicate of a simplex dimension never accepts the verbalized quotient of a unit of its
dimension ((26)). -/
theorem not_much_mathSpeak (hu : u.dimension = D) (hr : r.dimension ≠ 1) :
    ¬ much (w.quantity D) (mathSpeak n u r) x :=
  not_much_divisionMP hu hr

/-! ### The paper's examples -/

/-- The dimension a predicate measures in. -/
def predicateDimension? : String → Option QuantityDimension
  | "weight" => some (.of .mass)
  | "distance" => some (.of .length)
  | "density" => some .density
  | "speed" => some .speed
  | "pressure" => some .pressure
  | _ => none

/-- The measure term with symbol `s`. -/
def symbol? (s : String) : Option MeasureTerm := measureTerms.find? (·.symbol = s)

/-- The head unit of a row's measure phrase and, for a *per*-phrase, its *per*-unit, from its unit
nouns or from the symbols of the term it verbalizes (`13 g/mL`). -/
def units? (e : Datum) : Option (MeasureTerm × Option MeasureTerm) :=
  match e.feature? "verbalizes" with
  | some v =>
    match (v.toList.dropWhile (· ≠ ' ')).drop 1 |>.span (· ≠ '/') with
    | (a, _ :: b) => do pure (← symbol? (String.ofList a), some (← symbol? (String.ofList b)))
    | _ => none
  | none => do
    let u ← measureTerm? (← e.feature? "unit")
    match e.feature? "per_unit" with
    | none => pure (u, none)
    | some r => pure (u, some (← measureTerm? r))

/-- Whether a row's *per*-phrase is composed. A fronted *per*-PP has been, a verbalization of
notation has not, and otherwise the paper's classification decides. -/
def composed? (e : Datum) : Option Bool :=
  if e.feature? "diagnostic" = some "sub-extraction" then some true
  else if (e.feature? "verbalizes").isSome then some false
  else match e.feature? "interpretation" with
    | some "compositional" => some true
    | some "math speak" => some false
    | _ => none

/-- A row's predicate dimension and the dimension of its measure phrase's denotation. A bare
measure phrase and a composed *per*-phrase have the dimension of their head unit. -/
def dimensions? (e : Datum) : Option (QuantityDimension × QuantityDimension) := do
  let p ← predicateDimension? (← e.feature? "predicate_dimension")
  match ← units? e with
  | (u, none) => pure (p, u.dimension)
  | (u, some r) => pure (p, if ← composed? e then u.dimension else u.dimension / r.dimension)

/-- The measure phrase's dimension matches the predicate's exactly in the felicitous rows. -/
theorem rows_dimension : ∀ e ∈ Examples.all, ∀ p ∈ dimensions? e,
    (p.1 = p.2 ↔ e.judgment = .acceptable) := by
  decide +kernel

end

end BaleSchwarz2026
