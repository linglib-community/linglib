module

public import Linglib.Data.Examples.Huumo2020
public import Studies.Kiparsky1998

/-!
# Huumo (2020): Layers of (Un)boundedness

This file formalizes Huumo's account of quantified objects in Finnish. The case of the object
concerns the component events, each with one entity, and the quantifier the higher-order event
they make up: a quantity a quantifier delimits is bounded, so the higher-order event culminates
even when its component events do not. A time-frame adverbial measures a culminating event and a
measure phrase a non-culminating one, at the higher-order level or, with a number quantifier,
distributively. With Kiparsky's boundedness [the account derives the paper's aspectual
diagnostics](##rows_derived); [quantization in Krifka's sense fails them](##not_fits_quantization),
since a quantity [above a standard is bounded but not quantized](##exceedsStandard_bounded), and
so does [a single level of culmination](##not_fits_one_level).

## Implementation notes

* Huumo's "bounded (quantized)" is read as Kiparsky's boundedness: a quantity above a standard is
  not quantized in Krifka's sense, and Huumo cites no definition.
* Quantities are those of the four-individual model of `Kiparsky1998`; the standard of *paljon*
  'a lot of' and *usea* 'a number of' is two.
* Only number quantifiers distribute an adverbial over the component events.

## References

* [huumo-2020]
* [kiparsky-1998]
-/

@[expose] public section

namespace Huumo2020

open Kiparsky1998

/-- The quantifier of an object: none, a mass quantifier such as *paljon* 'a lot of', or a number
quantifier such as *usea* 'a number of'. -/
inductive Quantifier
  | none | mass | number
  deriving DecidableEq, Repr

/-- The time adverbial of a clause: a time-frame adverbial in the inessive, 'in an hour', or a
temporal measure phrase in the accusative, 'for an hour'. -/
inductive Adverbial
  | timeFrame | measure
  deriving DecidableEq, Repr

/-- A clause by its object's quantifier and case and its time adverbial. -/
structure Clause where
  quantifier : Quantifier
  case : Finnish.Case
  adverbial : Adverbial
  deriving DecidableEq, Repr

/-- The quantity *paljon* 'a lot of' and *usea* 'a number of' designate, one exceeding an implicit
standard. -/
def exceedsStandard : Finset (Finset (Fin 4)) := ofCard (2 < ·)

/-- A quantity above a standard is bounded, being cumulative but not divisive, though not
quantized. -/
theorem exceedsStandard_bounded :
    ¬ IsUnbounded (· ∈ exceedsStandard) ∧ ¬ Mereology.QUA (· ∈ exceedsStandard) :=
  ⟨by decide +kernel, mt isDiverse_iff_qua.2 (by decide +kernel)⟩

namespace Clause

variable (bounded : Finset (Finset (Fin 4)) → Prop) (c : Clause)

/-- The component events culminate when the object is accusative. -/
def ComponentCulminates : Prop := c.case = .acc

/-- The higher-order event culminates when a quantifier delimits a bounded quantity, and, without
a quantifier, when the object is accusative. -/
def Culminates : Prop :=
  match c.quantifier with
  | .none => c.case = .acc
  | _ => bounded exceedsStandard

/-- The adverbial fits the clause: a time-frame adverbial measures a culminating event and a
measure phrase a non-culminating one, either the higher-order event or, under a number
quantifier, each component event. -/
def Accepts : Prop :=
  match c.adverbial with
  | .timeFrame =>
    c.Culminates bounded ∨ (c.quantifier = .number ∧ c.ComponentCulminates)
  | .measure =>
    ¬ c.Culminates bounded ∨ (c.quantifier = .number ∧ ¬ c.ComponentCulminates)

instance [DecidablePred bounded] : Decidable (c.Accepts bounded) := by
  unfold Accepts Culminates ComponentCulminates; split <;> split <;> infer_instance

end Clause

/-- A row read through the paper's terms. -/
def Clause.ofDatum (e : Datum) : Option Clause := do
  let q ← e.parse? "quantifier" [("none", Quantifier.none), ("mass", .mass), ("number", .number)]
  let c ← e.parse? "case" [("part", Finnish.Case.part), ("acc", .acc)]
  let a ← e.parse? "adverbial" [("timeFrame", Adverbial.timeFrame), ("measure", .measure)]
  some ⟨q, c, a⟩

/-- The account fits the paper's diagnostics, all 14 read, when a quantity counts as bounded
under `bounded`. -/
def Fits (bounded : Finset (Finset (Fin 4)) → Prop) [DecidablePred bounded] : Prop :=
  Datum.Checks Clause.ofDatum (fun c ↦ Judgment.Band.ofProp (c.Accepts bounded)) Examples.all 14

instance (bounded : Finset (Finset (Fin 4)) → Prop) [DecidablePred bounded] :
    Decidable (Fits bounded) :=
  inferInstanceAs (Decidable (Datum.Checks _ _ _ _))

/-- With Kiparsky's boundedness the account derives which time adverbials the paper's clauses
accept, mass-quantified objects culminating like accusative ones and number-quantified
partitives culminating in the higher-order event. -/
theorem rows_derived : Fits fun d ↦ ¬ IsUnbounded (· ∈ d) := by
  decide +kernel

/-- Taking bounded quantities to be the quantized ones fails the diagnostics: a mass-quantified
object would not culminate. -/
theorem not_fits_quantization : ¬ Fits fun d ↦ IsDiverse (· ∈ d) := by
  decide +kernel

/-- A single level of culmination, on which the case of the object phrase decides whether the
event culminates: a time-frame adverbial fits an accusative or mass-quantified object and a
measure phrase a partitive one. -/
def Clause.AcceptsOneLevel (c : Clause) : Prop :=
  match c.adverbial with
  | .timeFrame => c.case = .acc ∨ c.quantifier = .mass
  | .measure => c.case = .part ∧ c.quantifier ≠ .mass

instance (c : Clause) : Decidable c.AcceptsOneLevel := by
  unfold Clause.AcceptsOneLevel; split <;> infer_instance

/-- A single level of culmination fails the number-quantified partitives that take a time-frame
adverbial. -/
theorem not_fits_one_level :
    ¬ Datum.Checks Clause.ofDatum (fun c ↦ Judgment.Band.ofProp c.AcceptsOneLevel)
      Examples.all 14 := by
  decide +kernel

end Huumo2020
