module

public import Linglib.Semantics.Degree.Measure.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Solt (2018): Proportional Comparatives and Relative Scales

*More residents of Ithaca than New York City know their neighbors* has a true reading that
compares proportions although the absolute counts point the other way. Solt accounts for it with
measurement: *many* and *few* are unambiguous gradable quantifiers, and a null head Meas
introduces a contextual measure function, monotone on the part-whole order, which may be
restricted to the parts of a totality and in particular be proportional. The rival ambiguity
account, after Partee and Romero, gives *many* and *few* a cardinal and a proportional entry.
The accounts part on the distribution of readings. With an individual-level predicate or in a
partitive the measure is domain-restricted, and then the positive form reads proportionally only
while the comparative keeps its cardinal reading; the ambiguity account predicts that both lose
it.

## Implementation notes

The paper reports the populations of Ithaca and New York City in prose and no counts of
residents who know their neighbours, so the divergence of the two readings is stated
symbolically: a smaller part is the larger share exactly when its totality is small enough.
Solt's other 2018 paper, the multidimensionality chapter, is formalized in
`Studies/Solt2018a.lean`.

## References

* [solt-2018b]
* [partee-1989]
* [romero-2015]
* [solt-2015]
* [schwarzschild-2006]
* [ahn-sauerland-2017]
* [carlson-1977]
* [milsark-1977]
-/

@[expose] public section

namespace Solt2018b

open Degree

variable {α : Type*} (μ : α → ℚ)

/-! ### The proportional measure function -/

/-- The proportional measure function gives a part's measure relative to the totality `tot`, and
0 when the totality has measure 0, as division by zero does. -/
def proportionalMeasure (tot y : α) : ℚ := μ y / μ tot

theorem proportionalMeasure_eq (tot y : α) : proportionalMeasure μ tot y = μ y / μ tot := rfl

theorem proportionalMeasure_zero (tot y : α) (h : μ tot = 0) :
    proportionalMeasure μ tot y = 0 := by
  rw [proportionalMeasure_eq, h, div_zero]

theorem proportionalMeasure_self_eq_one (tot : α) (htot : 0 < μ tot) :
    proportionalMeasure μ tot tot = 1 := by
  rw [proportionalMeasure_eq]
  exact div_self htot.ne'

theorem proportionalMeasure_monotonic [Preorder α] (hμ : StrictMono μ)
    (tot : α) {y z : α} (htot : 0 < μ tot) (hyz : y < z) :
    proportionalMeasure μ tot y < proportionalMeasure μ tot z := by
  rw [proportionalMeasure_eq, proportionalMeasure_eq]
  exact (div_lt_div_iff_of_pos_right htot).mpr (hμ hyz)

theorem proportionalMeasure_nonneg (hnn : ∀ x, 0 ≤ μ x) (tot y : α) :
    0 ≤ proportionalMeasure μ tot y :=
  div_nonneg (hnn y) (hnn tot)

theorem proportionalMeasure_le_one [Preorder α] (hμ : Monotone μ)
    (tot y : α) (hy : y ≤ tot) (htot : 0 < μ tot) :
    proportionalMeasure μ tot y ≤ 1 :=
  div_le_one_of_le₀ (hμ hy) htot.le

theorem proportionalMeasure_mem_unit_interval [Preorder α]
    (hnn : ∀ x, 0 ≤ μ x) (hμ : Monotone μ) (tot y : α) (hy : y ≤ tot) (htot : 0 < μ tot) :
    proportionalMeasure μ tot y ∈ Set.Icc (0 : ℚ) 1 :=
  ⟨proportionalMeasure_nonneg μ hnn tot y, proportionalMeasure_le_one μ hμ tot y hy htot⟩

theorem proportionalMeasure_const_mul (k : ℚ) (hk : k ≠ 0) (tot y : α) :
    proportionalMeasure (fun x ↦ k * μ x) tot y = proportionalMeasure μ tot y :=
  mul_div_mul_left _ _ hk

/-- *n percent of x are P* on the lexical entry for *percent* of [ahn-sauerland-2017],
which lexicalizes the division, holds exactly when the proportional measure of the
P-part of `x` is the degree `n / 100`, a point on the proportional scale. -/
theorem percent_iff_proportionalMeasure [SemilatticeInf α] (x p : α) (n : ℚ) :
    μ (x ⊓ p) / μ x = n / 100 ↔ proportionalMeasure μ x (x ⊓ p) = n / 100 := Iff.rfl

/-! ### The two readings of a quantity comparative -/

/-- On the cardinal reading, *more A than B Q* says that the A-part with the property outmeasures
the B-part. -/
def CardinalReading (a b : α) : Prop := μ b < μ a

/-- On the proportional reading, where the measure `Meas` introduces is proportional to each
clause's totality, *more A than B Q* says that the A-part is the larger share of its totality. -/
def ProportionalReading (A B a b : α) : Prop :=
  proportionalMeasure μ B b < proportionalMeasure μ A a

theorem proportionalReading_iff {A B a b : α} (hA : 0 < μ A) (hB : 0 < μ B) :
    ProportionalReading μ A B a b ↔ μ b * μ A < μ a * μ B := by
  rw [ProportionalReading, proportionalMeasure_eq, proportionalMeasure_eq, div_lt_div_iff₀ hB hA]

/-- The readings come apart, since a part that is outmeasured by the other is nonetheless the
larger share whenever its totality is small enough, as with Ithaca's thirty thousand
residents against New York City's eight million. -/
theorem readings_diverge {A B a b : α} (hA : 0 < μ A) (hB : 0 < μ B)
    (h : μ a < μ b) (h' : μ b * μ A < μ a * μ B) :
    ¬ CardinalReading μ a b ∧ ProportionalReading μ A B a b :=
  ⟨not_lt.2 h.le, (proportionalReading_iff μ hA hB).2 h'⟩

/-! ### The distribution of readings -/

/-- The measure function `Meas` introduces is unrestricted, restricted to the parts of a
totality, or the proportional special case of the latter. -/
inductive MeasureKind where
  | unrestricted
  | domainRestricted
  | proportional
  deriving DecidableEq, Repr

/-- The kinds whose range is a bounded segment of the scale. -/
def MeasureKind.IsRestricted : MeasureKind → Prop
  | .unrestricted => False
  | .domainRestricted => True
  | .proportional => True

instance (k : MeasureKind) : Decidable k.IsRestricted := by
  cases k <;> unfold MeasureKind.IsRestricted <;> infer_instance

/-- Cardinal or proportional reading of a quantity word. -/
inductive Reading where
  | cardinal
  | proportional
  deriving DecidableEq, Repr

/-- The positive form, bound by the positive morpheme, and the comparative. -/
inductive QForm where
  | positive
  | comparative
  deriving DecidableEq, Repr

/-- How each form reads a kind of measure. The comparative compares the degrees the
measure delivers, cardinal unless the measure is proportional. The positive morpheme's
standard range sits inside the bounded segment that is a restricted measure's range, so
either restricted kind gives the positive form its proportional reading. -/
def reading : QForm → MeasureKind → Reading
  | .comparative, .proportional => .proportional
  | .comparative, _ => .cardinal
  | .positive, .unrestricted => .cardinal
  | .positive, _ => .proportional

/-- A context whose available kinds are `allowed` licenses a reading of a form when some
available kind yields it. -/
def Licensed (allowed : MeasureKind → Prop) (f : QForm) (r : Reading) : Prop :=
  ∃ k, allowed k ∧ reading f k = r

theorem unrestricted_licensed (f : QForm) (r : Reading) : Licensed (fun _ ↦ True) f r := by
  cases f <;> cases r <;> first
    | exact ⟨.unrestricted, trivial, rfl⟩
    | exact ⟨.proportional, trivial, rfl⟩

theorem restricted_positive_iff (r : Reading) :
    Licensed MeasureKind.IsRestricted .positive r ↔ r = .proportional := by
  constructor
  · rintro ⟨k, hk, rfl⟩; cases k <;> simp_all [MeasureKind.IsRestricted, reading]
  · rintro rfl; exact ⟨.domainRestricted, trivial, rfl⟩

/-- With only restricted kinds available, under an individual-level predicate or in a partitive,
the comparative keeps its cardinal reading through an ordinary domain-restricted measure while
the positive form loses it. -/
theorem restricted_asymmetry :
    Licensed MeasureKind.IsRestricted .comparative .cardinal ∧
    ¬ Licensed MeasureKind.IsRestricted .positive .cardinal :=
  ⟨⟨.domainRestricted, trivial, rfl⟩, by simp [restricted_positive_iff]⟩

/-- The ambiguity account has a cardinal and a proportional entry, and no
relative-but-not-proportional measurement. -/
def ambiguityKinds : MeasureKind → Prop
  | .domainRestricted => False
  | _ => True

/-- On the ambiguity account, whatever confines the positive form to its proportional
reading confines the comparative too. With the inventory reduced to the proportional
entry, both forms read alike, and the cardinal reading of *more residents of Ithaca than
New York City know their neighbors* is lost. -/
theorem ambiguity_symmetric (r : Reading) :
    Licensed (fun k ↦ ambiguityKinds k ∧ k.IsRestricted) .positive r ↔
      Licensed (fun k ↦ ambiguityKinds k ∧ k.IsRestricted) .comparative r := by
  constructor <;> rintro ⟨k, hk, rfl⟩ <;>
    cases k <;> simp_all [ambiguityKinds, MeasureKind.IsRestricted, reading] <;>
    exact ⟨.proportional, ⟨trivial, trivial⟩, rfl⟩

end Solt2018b
