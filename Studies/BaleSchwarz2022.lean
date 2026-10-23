module

public import Linglib.Semantics.Degree.Measure.Quantity
public import Linglib.Fragments.English.MeasurePhrases
public import Linglib.Data.Examples.BaleSchwarz2022
public import Mathlib.Data.PFun
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum

/-!
# Bale and Schwarz (2022): Measurements from "per" without complex dimensions

On Coppock's division theory the preposition *per* divides quantities, so that *0.9 grams per
milliliter* denotes the density `0.9 g/mL`. On Bale and Schwarz's anaphoric theory *per
milliliter* measures a covert pronoun in milliliters, a pure number that multiplies `0.9 g`, and
the measure phrase stays in the dimension of mass. The division theory undergenerates: *weigh*
measures weight, so it cannot take a quotient, and the polysemous *weigh* that would let it
predicts a same-density reading of *this cube weighs what that cube weighs* that the sentence
lacks. It also overgenerates: it gives *0.1 grams per milliliter* and *0.1 kilograms per liter*
one meaning, while the anaphoric *per*, which sees the pronoun's referent, presupposes that the
referent measures at least one unit. Where both theories compose they agree.

A world assigns each dimension a real-valued measure function, and the units are the English
measure terms.

## Main statements

* `not_much_divisionMP`: a measurement verb never takes a measure phrase of the division theory
  whose head unit measures in the verb's dimension.
* `density_reading`: the polysemous *weigh* makes *this cube weighs what that cube weighs* true
  of a one-kilogram and a two-kilogram cube.
* `anaphoricMP_snd`: an anaphoric measure phrase has the dimension of its head unit.
* `much_divisionMP_iff_anaphoricMP`, `contains_divisionMP_iff_anaphoricMP`: where both theories
  compose, they derive the same truth conditions.
* `divisionMP_kilogram_liter`: the division theory identifies *0.1 kilograms per liter* with
  *0.1 grams per milliliter*.
* `unit_sensitivity`: on the anaphoric theory the two pseudo-partitives assert the same thing,
  but one presupposes a volume of at least a milliliter and the other of at least a liter.
* `division_overgenerates`: at a world where the sample measures a tenth of a milliliter, the
  division theory makes *the 0.1 milliliter sample contained 0.1 grams of salt per milliliter*
  true, while on the anaphoric theory it is undefined.
* `acceptable_iff_mem_dom`: a *per*-sentence is defined at a world where its subject measures as
  the example states exactly when the example is felicitous.
* `density_ne_anaphoricMP`: the anaphoric theory makes *the sample's density is 0.9 grams per
  milliliter* contradictory, the puzzle the paper ends on.

## Implementation notes

* A sentence with *per* denotes a partial proposition `World E →. Prop`, after the
  Heim–Kratzer notation of (43). It maps its truth conditions over the value of the *per*-phrase,
  so the sentence is defined where *per* is: the global projection the paper assumes (p. 557).
* The covert pronoun is a parameter, resolved to the matrix subject.
* (43) compares two quantities of one dimension; the file compares their magnitudes.
* The papers' dimension WT of *weigh* and of *grams* is mass.

## References

* [bale-schwarz-2022]
* [coppock-2021]
* [heim-kratzer-1998]
* [nakanishi-2007]
* [schwarzschild-2006]
-/

@[expose] public section

namespace BaleSchwarz2022

open Degree Quantity English.MeasurePhrases

noncomputable section

variable {E : Type*}

/-- A world assigns each dimension `D` its measure function `μ_D`. -/
abbrev World (E : Type*) := QuantityDimension → E → ℝ

/-- `w.quantity D x` is `μ_D(x)`, a quantity of dimension `D`. -/
def World.quantity (w : World E) (D : QuantityDimension) (x : E) : Quantity ℝ := (w D x, D)

@[simp] theorem World.quantity_fst (w : World E) (D : QuantityDimension) (x : E) :
    (w.quantity D x).1 = w D x := rfl

@[simp] theorem World.quantity_snd (w : World E) (D : QuantityDimension) (x : E) :
    (w.quantity D x).2 = D := rfl

variable {w : World E} {D : QuantityDimension} {x y m : E} {q : Quantity ℝ} {n k : ℝ}
  {u u' r r' : MeasureTerm} {salt : E → Prop} {contain : E → E → Prop}

/-! ### Measure predication -/

/-- `much μ q x` says that `x` measures `q` under `μ`, `λq λx. μ(x) = q`. It is the measurement
verb *weigh* with `μ = μ_WT` ((5)), and the covert `MUCH` of pseudo-partitives with `μ`
underspecified ((25)). -/
def much (μ : E → Quantity ℝ) (q : Quantity ℝ) (x : E) : Prop := μ x = q

theorem much_quantity_iff : much (w.quantity D) q x ↔ w D x = q.1 ∧ q.2 = D := by
  simp [much, Prod.ext_iff, eq_comm]

theorem not_much_quantity_of_snd_ne (h : q.2 ≠ D) : ¬ much (w.quantity D) q x := by
  simp [much_quantity_iff, h]

/-- `contains salt contain μ q m` says that `m` contains salt of measure `q` under `μ`,
`∃x[salt(x) ∧ μ(x) = q ∧ contain(m, x)]` ((26)). -/
def contains (salt : E → Prop) (contain : E → E → Prop) (μ : E → Quantity ℝ) (q : Quantity ℝ)
    (m : E) : Prop :=
  ∃ x, salt x ∧ much μ q x ∧ contain m x

/-! ### The division theory -/

/-- Coppock's *per* divides its second argument by its first, `⟦per⟧ = λr λq. q / r` ((1)). -/
def divisionPer (r q : Quantity ℝ) : Quantity ℝ := q / r

/-- On the division theory *n u per r* denotes the quotient `n u / r` ((2)). -/
def divisionMP (n : ℝ) (u r : MeasureTerm) : Quantity ℝ :=
  divisionPer r.quantity (pure n * u.quantity)

@[simp] theorem divisionMP_snd : (divisionMP n u r).2 = u.dimension / r.dimension := by
  simp [divisionMP, divisionPer]

/-- The division theory undergenerates ((7)). A measure of dimension `D` never equates with
*n u per r* for a unit `u` of `D`, since the phrase has `D` divided by the dimension of `r`. -/
theorem not_much_divisionMP (hu : u.dimension = D) (hr : r.dimension ≠ 1) :
    ¬ much (w.quantity D) (divisionMP n u r) x :=
  not_much_quantity_of_snd_ne (by simpa [hu])

/-- The polysemous *weigh* of (8) measures density, `μ_{WT/VOL}`. -/
def density (w : World E) (x : E) : Quantity ℝ :=
  w.quantity (.of .mass) x / w.quantity .volume x

/-- With the free relative denoting `y`'s measure, *x weighs what y weighs* equates the two
measures ((12)). -/
theorem much_quantity_quantity_iff : much (w.quantity D) (w.quantity D y) x ↔ w D x = w D y := by
  simp [much_quantity_iff]

/-- The polysemous *weigh* gives *this cube weighs what that cube weighs* a same-density reading
((13)) that is true of a one-kilogram and a two-kilogram cube, where the weight reading ((12)) is
false. -/
theorem density_reading :
    ∃ w : World (Fin 2), much (density w) (density w 1) 0 ∧
      ¬ much (w.quantity (.of .mass)) (w.quantity (.of .mass) 1) 0 := by
  refine ⟨fun D i ↦ (i.val + 1 : ℝ) * if D = .of .mass then 1000 else 1, ?_, ?_⟩
  · ext <;> simp [density, show QuantityDimension.volume ≠ .of .mass by decide]
    norm_num
  · simp [much_quantity_iff]

/-! ### The anaphoric theory -/

/-- Bale and Schwarz's *per* measures its pronoun's referent in units of its quantity argument,
`⟦per⟧ = λq λx. μ_dim(q)(x) / q` ((16)), a pure number. -/
def anaphoricPer (w : World E) (r : MeasureTerm) (y : E) : Quantity ℝ :=
  w.quantity r.dimension y / r.quantity

@[simp] theorem anaphoricPer_fst :
    (anaphoricPer w r y).1 = w r.dimension y / r.magnitude := rfl

@[simp] theorem anaphoricPer_snd : (anaphoricPer w r y).2 = 1 := by simp [anaphoricPer]

/-- The anaphoric *n u per r*, its pronoun resolved to `y`, denotes `n u ⋅ μ_dim(r)(y) / r`
((18)). -/
def anaphoricMP (w : World E) (n : ℝ) (u r : MeasureTerm) (y : E) : Quantity ℝ :=
  pure n * u.quantity * anaphoricPer w r y

@[simp] theorem anaphoricMP_fst :
    (anaphoricMP w n u r y).1 = n * u.magnitude * (w r.dimension y / r.magnitude) := rfl

/-- The anaphoric measure phrase stays in its head unit's dimension ((19)). -/
@[simp] theorem anaphoricMP_snd : (anaphoricMP w n u r y).2 = u.dimension := by
  simp [anaphoricMP]

/-- The measurement-verb sentence composes ((22)) to `μ_D(x) = n u ⋅ μ_dim(r)(y) / r`. -/
theorem much_anaphoricMP_iff (hu : u.dimension = D) :
    much (w.quantity D) (anaphoricMP w n u r y) x ↔
      w D x = n * u.magnitude * (w r.dimension y / r.magnitude) := by
  simp [much_quantity_iff, hu]

/-- Where both theories compose they agree, on (9) and (22) with the pronoun's referent the
subject and on (31) and (32) with it the container. -/
theorem much_divisionMP_iff_anaphoricMP (hy : w r.dimension y ≠ 0) :
    much (fun x ↦ w.quantity D x / w.quantity r.dimension y) (divisionMP n u r) x ↔
      much (w.quantity D) (anaphoricMP w n u r y) x := by
  rw [much, much, (Quantity.isUnit_iff.2 hy).div_eq_iff, divisionMP, divisionPer, anaphoricMP,
    anaphoricPer, div_mul_eq_mul_div, mul_div_assoc]

theorem contains_divisionMP_iff_anaphoricMP (hm : w r.dimension m ≠ 0) :
    contains salt contain (fun x ↦ w.quantity D x / w.quantity r.dimension m)
        (divisionMP n u r) m ↔
      contains salt contain (w.quantity D) (anaphoricMP w n u r m) m :=
  exists_congr fun _ ↦ and_congr_right fun _ ↦ and_congr_left fun _ ↦
    much_divisionMP_iff_anaphoricMP hm

/-! ### Units of different sizes -/

/-- The division theory identifies measure phrases whose units are scaled alike ((36b)). -/
theorem divisionMP_scales (hk : k ≠ 0) (hu : u'.quantity = pure k * u.quantity)
    (hr : r'.quantity = pure k * r.quantity) :
    divisionMP n u' r' = divisionMP n u r := by
  rw [divisionMP, divisionMP, divisionPer, divisionPer, hu, hr, mul_left_comm,
    (Quantity.isUnit_iff (q := pure k)).2 hk |>.mul_div_mul_left]

/-- So it gives *0.1 kilograms per liter* the meaning of *0.1 grams per milliliter*, since
`kg / L = g / mL` ((36)). -/
theorem divisionMP_kilogram_liter : divisionMP n kilogram liter = divisionMP n gram milliliter :=
  divisionMP_scales (by norm_num) kilogram_quantity liter_quantity

theorem anaphoricMP_scales (hk : k ≠ 0) (hu : u'.quantity = pure k * u.quantity)
    (hr : r'.quantity = pure k * r.quantity) :
    anaphoricMP w n u' r' y = anaphoricMP w n u r y := by
  rw [MeasureTerm.quantity_eq_pure_mul_iff] at hu hr
  ext
  · simp only [anaphoricMP_fst, hu.1, hr.1, hr.2]; field_simp
  · simp [hu.2]

/-! ### The copular puzzle -/

/-- No quantity of mass is a density, so *the sample's density is 0.9 grams* ((47)) is
contradictory. -/
theorem density_ne_of_snd (hq : q.2 = .of .mass) : density w x ≠ q := fun h ↦ by
  simpa [density, hq] using congrArg Prod.snd h

theorem density_ne_pure_mul (hu : u.dimension = .of .mass) :
    density w x ≠ pure n * u.quantity :=
  density_ne_of_snd (by simp [hu])

/-- On the anaphoric theory so is *the sample's density is 0.9 grams per milliliter* ((46)),
which reports the sample's density. -/
theorem density_ne_anaphoricMP (hu : u.dimension = .of .mass) :
    density w x ≠ anaphoricMP w n u r y :=
  density_ne_of_snd (by simp [hu])

/-- On the division theory (46) equates the sample's density with `n u / r`. -/
theorem density_eq_divisionMP_iff (hu : u.dimension = .of .mass) (hr : r.dimension = .volume) :
    density w x = divisionMP n u r ↔
      w (.of .mass) x / w .volume x = n * u.magnitude / r.magnitude := by
  simp [density, divisionMP, divisionPer, Prod.ext_iff, hu, hr]

/-! ### Unit sensitivity -/

section UnitSensitivity

/-- The revised *per* of (43), `λq λx: μ_dim(q)(x) ≥ q. μ_dim(q)(x) / q`, is `anaphoricPer`
restricted to the referents that measure at least one unit. -/
def per (w : World E) (r : MeasureTerm) : E →. Quantity ℝ :=
  PFun.res (anaphoricPer w r) {y | (r.magnitude : ℝ) ≤ w r.dimension y}

theorem mem_dom_per : y ∈ (per w r).Dom ↔ (r.magnitude : ℝ) ≤ w r.dimension y := Iff.rfl

/-- `perSentence r y φ` is a sentence whose *per*-phrase, its pronoun resolved to `y`, feeds the
truth conditions `φ`. At each world it maps `φ` over the phrase's value, so the sentence is
defined where *per* is. -/
def perSentence (r : MeasureTerm) (y : E) (φ : World E → Quantity ℝ → Prop) :
    World E →. Prop :=
  fun w ↦ (per w r y).map (φ w)

variable {φ : World E → Quantity ℝ → Prop}

theorem perSentence_eq_res : perSentence r y φ =
    PFun.res (fun w ↦ φ w (anaphoricPer w r y)) {w | (r.magnitude : ℝ) ≤ w r.dimension y} := rfl

@[simp] theorem mem_dom_perSentence :
    w ∈ (perSentence r y φ).Dom ↔ (r.magnitude : ℝ) ≤ w r.dimension y := Iff.rfl

/-- *y weighs n u per r*, the pronoun resolved to the subject ((20)). -/
def weighs (n : ℝ) (u r : MeasureTerm) (y : E) : World E →. Prop :=
  perSentence r y fun w a ↦ much (w.quantity (.of .mass)) (pure n * u.quantity * a) y

/-- *m contains n u per r of salt*, the pronoun resolved to the container ((41)). -/
def containsPer (salt : E → Prop) (contain : E → E → Prop) (n : ℝ) (u r : MeasureTerm) (m : E) :
    World E →. Prop :=
  perSentence r m fun w a ↦
    contains salt contain (w.quantity (.of .mass)) (pure n * u.quantity * a) m

theorem weighs_scales (hk : k ≠ 0) (hu : u'.quantity = pure k * u.quantity)
    (hr : r'.quantity = pure k * r.quantity) :
    weighs n u' r' y =
      PFun.res (fun w ↦ much (w.quantity (.of .mass)) (anaphoricMP w n u r y) y)
      {w | k * r.magnitude ≤ w r.dimension y} := by
  obtain ⟨hm, hd⟩ := MeasureTerm.quantity_eq_pure_mul_iff.mp hr
  rw [weighs, perSentence_eq_res, hm, hd]
  congr
  funext w
  rw [← anaphoricMP_scales hk hu hr]; rfl

theorem containsPer_scales (hk : k ≠ 0) (hu : u'.quantity = pure k * u.quantity)
    (hr : r'.quantity = pure k * r.quantity) :
    containsPer salt contain n u' r' m =
      PFun.res (fun w ↦ contains salt contain (w.quantity (.of .mass)) (anaphoricMP w n u r m) m)
        {w | k * r.magnitude ≤ w r.dimension m} := by
  obtain ⟨hm, hd⟩ := MeasureTerm.quantity_eq_pure_mul_iff.mp hr
  rw [containsPer, perSentence_eq_res, hm, hd]
  congr
  funext w
  rw [← anaphoricMP_scales hk hu hr]; rfl

/-- The anaphoric theory is unit sensitive ((27), (36)). *The mixture contains 0.1 grams per
milliliter of salt* and *the mixture contains 0.1 kilograms per liter of salt* assert the same
thing, but the first presupposes that the mixture measures at least a milliliter and the second
at least a liter. -/
theorem unit_sensitivity :
    ∃ A : World E → Prop,
      containsPer salt contain n gram milliliter m = PFun.res A {w | 1 ≤ w .volume m} ∧
      containsPer salt contain n kilogram liter m = PFun.res A {w | 1000 ≤ w .volume m} := by
  refine ⟨fun w ↦
    contains salt contain (w.quantity (.of .mass)) (anaphoricMP w n gram milliliter m) m,
    ?_, ?_⟩
  · rw [containsPer, perSentence_eq_res]; congr 1; ext; simp [milliliter]
  · rw [containsPer_scales (by norm_num) kilogram_quantity liter_quantity]
    congr 1; ext; simp [milliliter]

/-- The division theory's truth conditions for *m contains n u per r of salt* ((31)) can hold
whatever `m` measures in the *per*-unit's dimension. -/
theorem contains_divisionMP_satisfiable (hu : u.dimension = .of .mass) {v : ℝ} (hv : v ≠ 0) :
    ∃ w : World (Fin 2), w r.dimension 0 = v ∧
      contains (· = 1) (fun a b ↦ a = 0 ∧ b = 1)
        (fun x ↦ w.quantity (.of .mass) x / w.quantity r.dimension 0) (divisionMP n u r) 0 := by
  refine ⟨fun D i ↦ if i = 0 then (if D = r.dimension then v else 0)
    else if D = .of .mass then n * u.magnitude / r.magnitude * v else 0, by simp, 1, rfl, ?_, rfl,
    rfl⟩
  ext
  · simp [divisionMP, divisionPer]
    field_simp
  · simp [hu]

/-- So the division theory overgenerates ((38b)). Where the sample measures a tenth of a
milliliter it makes *the 0.1 milliliter sample contained 0.1 grams of salt per milliliter* true,
while on the anaphoric theory the sentence is undefined there. -/
theorem division_overgenerates :
    ∃ w : World (Fin 2),
      contains (· = 1) (fun a b ↦ a = 0 ∧ b = 1)
        (fun x ↦ w.quantity (.of .mass) x / w.quantity .volume 0)
        (divisionMP (1 / 10) gram milliliter) 0 ∧
      w ∉ (containsPer (· = 1) (fun a b ↦ a = 0 ∧ b = 1) (1 / 10) gram milliliter 0).Dom := by
  obtain ⟨w, hw, h⟩ := contains_divisionMP_satisfiable (n := 1 / 10) (r := milliliter) (u := gram)
    rfl (v := 1 / 10) (by norm_num)
  refine ⟨w, h, ?_⟩
  simp only [containsPer, mem_dom_perSentence, hw]
  norm_num [milliliter]

/-! ### The paper's examples -/

/-- An example's *per*-unit, and the measure in that unit's dimension that its subject is stated
to have, in the dimension's reference unit. -/
structure Scenario where
  per : MeasureTerm
  subjectMeasure : ℚ

/-- `scenario? e` reads the scenario off a row that states its subject's measure. -/
def scenario? (e : Datum) : Option Scenario := do
  let per ← measureTerm? (← e.feature? "per_unit")
  let m ← e.decimal? "subject_measure"
  let su ← measureTerm? (← e.feature? "subject_unit")
  guard (su.dimension = per.dimension)
  pure ⟨per, m * su.magnitude⟩

/-- The subject measures at least one *per*-unit exactly in the felicitous examples ((37), (38),
(44), (45)). -/
theorem rows_unit_sensitivity : ∀ e ∈ Examples.all, ∀ s ∈ scenario? e,
    (s.per.magnitude ≤ s.subjectMeasure ↔ e.judgment = .acceptable) := by
  decide +kernel

/-- At a world where its subject measures as the example states, a *per*-sentence is defined
exactly when the example is felicitous. -/
theorem acceptable_iff_mem_dom {e : Datum} (he : e ∈ Examples.all)
    {s : Scenario} (hs : s ∈ scenario? e) (hy : w s.per.dimension y = s.subjectMeasure) :
    e.judgment = .acceptable ↔ w ∈ (perSentence s.per y φ).Dom := by
  rw [mem_dom_perSentence, hy, Rat.cast_le]
  exact (rows_unit_sensitivity e he s hs).symm

end UnitSensitivity

end

end BaleSchwarz2022
