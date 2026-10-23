module

public import Linglib.Semantics.Reference.Rigidity
public import Linglib.Semantics.Degree.MeasurePhrase
public import Linglib.Semantics.Degree.Delineation
public import Linglib.Data.Examples.VonStechow1984
public import Mathlib.Tactic.Linarith

/-!
# von Stechow (1984): Comparing Semantic Theories of Comparison

Von Stechow compares eight semantic theories of the comparative against his own synthesis, in
which a than-clause denotes a Russellian definite description of a degree and may carry an
ACTUALLY operator. Russell's yacht ambiguity is the presence or absence of ACTUALLY in the
than-clause, a disjunctive than-clause entails both disjuncts, a modal comparative compares maxima
over the accessible worlds, and Klein's degree-free ordering agrees with degree comparison on
simple comparatives but not on differentials and factor phrases.

## Main results

* `deDicto_absurd`: the de dicto reading of the yacht sentence (1) is contradictory.
* `disjunction_to_conjunction_in_than`: a disjunctive than-clause entails both disjuncts, (v).
* `maxDeg_witness`: a modal comparative compares maxima over the accessible worlds, (x).
* `klein_agrees_on_simple`: Klein's ordering agrees with degree comparison on simple
  comparatives, (171).
* `moreSem_exceeds_counterfactual_worlds`: *too* (R13) is the additive *more* of R4 against a
  counterfactually determined threshold, (227).

## Implementation notes

Degrees form a linear order, with the additive or multiplicative structure the rule at hand
needs; measures are world-indexed where ACTUALLY matters and extensional otherwise. The
descriptive-adequacy table (xvii) over the eight theories is not transcribed, and the rules R6
to R12 for the positive, nominal, mass and adverbial comparatives are not formalized. The
paper's examples are the rows of `Data.Examples.VonStechow1984`.

## References

* [von-stechow-1984]
* [russell-1905]
* [klein-1980]
-/

@[expose] public section

namespace VonStechow1984

open Degree

variable {W Entity D : Type*} [LinearOrder D]

/-! ### Intensional degree semantics (§§II–V)

`deReComparative` vs `deDictoComparative` is von Stechow's analysis of
Russell's ambiguity ((1), `Examples.yacht`): the than-clause standard is
either ACTUALLY-anchored to the actual world or evaluated in the belief
world — no degree-operator scope is involved. The ambiguous counterfactual
((26), `Examples.ex26`, §III) works the same way: its trivial reading's
clauses are de dicto self-comparisons, contradictory by `deDicto_absurd`. -/

/-- The comparative between world-indexed measures, R3, holds when `a` exceeds `b` at `w`. -/
def intensionalComparative (μ : W → Entity → D) (w : W) (a b : Entity) : Prop :=
  μ w a > μ w b

theorem intensionalComparative_rigid (μe : Entity → D) (w : W) (a b : Entity) :
    intensionalComparative (fun _ ↦ μe) w a b ↔ μe b < μe a :=
  Iff.rfl

/-- On the de re reading of *I thought your yacht was larger than it is* the than-clause standard is
ACTUALLY-anchored, evaluated at the actual world `w₀`, while the matrix is evaluated at the belief
world `wBel`. -/
def deReComparative (μ : W → Entity → D) (w₀ wBel : W) (x : Entity) : Prop :=
  μ wBel x > μ w₀ x

/-- The de dicto reading has no ACTUALLY, so standard and matrix are both evaluated at `wBel`. -/
def deDictoComparative (μ : W → Entity → D) (wBel : W) (x : Entity) : Prop :=
  μ wBel x > μ wBel x

/-- The de dicto reading is contradictory. -/
theorem deDicto_absurd (μ : W → Entity → D) (wBel : W) (x : Entity) :
    ¬ deDictoComparative μ wBel x :=
  lt_irrefl _

-- Russell's yacht ((1), `Examples.yacht`): actual length 5, believed length 8.
private def yachtLength : Bool → Unit → ℕ
  | true,  () => 5
  | false, () => 8

-- De re: the believed length exceeds the actual length. Consistent.
example : deReComparative yachtLength true false () := by
  simp [deReComparative, yachtLength]

-- De dicto: contradictory.
example : ¬ deDictoComparative yachtLength false () :=
  deDicto_absurd yachtLength false ()

/-- In (v) (`Examples.exV`, §§VI–VII) a disjunctive standard entails both disjuncts, the
downward-entailingness of the than-clause that also licenses its NPIs
(`Ladusaw1979.IsDownwardEntailing .clausalComparative`). -/
theorem disjunction_to_conjunction_in_than (μa μb μc : D)
    (h : μb ⊔ μc < μa) : μb < μa ∧ μc < μa :=
  sup_lt_iff.mp h

/-- If the greatest accessible A-degree exceeds the greatest B-degree, some accessible A-world beats
every B-world ((x), `Examples.exX`, §VIII). -/
theorem maxDeg_witness {acc : Set W} {μA μB : W → D} {maxA maxB : D}
    (hmaxA : IsGreatest (μA '' acc) maxA) (hmaxB : IsGreatest (μB '' acc) maxB)
    (hgt : maxB < maxA) :
    ∃ w ∈ acc, ∀ v ∈ acc, μB v < μA w := by
  obtain ⟨w, hw, rfl⟩ := hmaxA.1
  exact ⟨w, hw, fun v hv ↦ lt_of_le_of_lt (hmaxB.2 ⟨v, hv, rfl⟩) hgt⟩

/-- Klein's degree-free ordering ([klein-1980]; §XI) matches degree
comparison on simple comparatives via `Delineation.ofMeasure`; the divergence
is confined to differential and factor constructions ((171a)–(171c)). -/
theorem klein_agrees_on_simple (μ : Entity → D) (cc : Set Entity)
    (a b : Entity) (ha : a ∈ cc) (hb : b ∈ cc) :
    μ b < μ a ↔
      (Delineation.ofMeasure μ).Outranks cc a b :=
  (Delineation.outranks_ofMeasure_iff μ ha hb).symm

/-! ### Synthesis rules R4 (`moreSem`), R5 (`asSem`), R13 (*too*) (§XIII) -/

/-- Synthesis rule R4 makes `⟦more⟧(d₁)(A⁰)(d₂)(x)` hold iff `A⁰(x, d₁ + d₂)` with monotone `A⁰`,
the differential `d₁` plus the than-clause maximum `d₂`. -/
def moreSem [Add D] (μ : Entity → D) (x : Entity) (d₁ d₂ : D) : Prop :=
  d₁ + d₂ ≤ μ x

/-- Synthesis rule R5 makes `⟦as⟧` multiply where R4 adds (*twice as fat*, (171b)). -/
def asSem [Mul D] (μ : Entity → D) (x : Entity) (d₁ d₂ : D) : Prop :=
  d₁ * d₂ ≤ μ x

theorem moreSem_comparative_bridge [AddCommMonoid D] [IsOrderedCancelAddMonoid D]
    (μ : Entity → D) (a b : Entity) {d₁ : D} (hd₁ : 0 < d₁)
    (h : moreSem μ a d₁ (μ b)) : μ b < μ a :=
  (lt_add_of_pos_left (μ b) hd₁).trans_le h

theorem moreSem_differential_bridge [AddCommGroup D] [IsOrderedAddMonoid D]
    (μ : Entity → D) (a b : Entity) (diff : D)
    (h : DifferentialComparative μ a b diff) : moreSem μ a diff (μ b) :=
  le_of_eq (by rw [← h, sub_add_cancel])

theorem asSem_equative_bridge [MulOneClass D] (μ : Entity → D) (a b : Entity) :
    asSem μ a 1 (μ b) ↔ μ b ≤ μ a := by
  simp [asSem, one_mul]

theorem asSem_factor_bridge [Mul D] (μ : Entity → D) (a b : Entity)
    (factor : D) (h : FactorEquative μ a b factor) : asSem μ a factor (μ b) :=
  le_of_eq h.symm

/-- With a greatest threshold over the accessible worlds, being `excess` too `A` puts the actual
degree above every accessible world's (R13, §XIII). -/
theorem moreSem_exceeds_counterfactual_worlds
    [AddCommMonoid D] [IsOrderedCancelAddMonoid D]
    (μ : W → Entity → D) (w₀ : W) (acc : Set W) (x : Entity)
    {threshold excess : D} (hexcess : 0 < excess)
    (hmax : IsGreatest ((fun w ↦ μ w x) '' acc) threshold)
    (htoo : moreSem (μ w₀) x excess threshold) :
    ∀ w ∈ acc, μ w x < μ w₀ x :=
  fun w hw ↦ (hmax.2 ⟨w, hw, rfl⟩).trans_lt
    ((lt_add_of_pos_left threshold hexcess).trans_le htoo)

-- (227) (`Examples.ex227`): an 80 kg pack with a 30 kg liftable
-- threshold is at least 50 kg too heavy.
example : moreSem (fun _ : Unit ↦ (80 : ℚ)) () 50 30 := by
  norm_num [moreSem]

end VonStechow1984
