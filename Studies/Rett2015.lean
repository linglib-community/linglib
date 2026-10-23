module

public import Linglib.Data.Examples.Rett2015
public import Linglib.Fragments.English.Adjectives
public import Linglib.Semantics.Degree.Antonymy
public import Linglib.Semantics.Degree.Defs

/-!
# Rett (2015): The semantics of evaluativity

Rett derives the distribution of evaluativity across degree constructions, her Table 3.1, from two
Neo-Gricean implicatures. A Quantity implicature strengthens the otherwise tautological positive
construction, and the Marked Meaning Principle, after Horn's division of pragmatic labor, makes the
marked, negative antonym evaluative in exactly the polar-invariant constructions, the equatives
and degree questions in which its unmarked antonym has the same truth conditions.

## Main results

* `evaluative_iff_observed`: the implicature route, `implicature`, predicts every judgment of the
  table.
* `exact_equative_antonym_invariant`, `comparative_antonym_variant`: polar invariance grounded in
  the comparison semantics, the strengthened equatives of two antonyms being mutually entailing and
  their comparatives excluding each other.

## Implementation notes

Antonym polarity is the adjective's `Adjective.polarity`, which acts on the comparison of its
equative and comparative through the order dual, `Polarity.negative • c = c.dual`; negative antonyms
are the marked members of their pairs (Bierwisch, Kennedy). The positive
construction and the measure phrase have no polarity-parametrized semantics in the substrate,
so their rows of `IsPolarInvariant` are the book's classification.

## References

* [J. Rett, *The semantics of evaluativity* (2015)][rett-2015]
* [L. R. Horn, *Toward a new taxonomy for pragmatic inference: Q-based and R-based
  implicature* (1984)][horn-1984]
* [M. Bierwisch, *The semantics of gradation* (1989)][bierwisch-1989]
* [C. Kennedy, *Vagueness and grammar: the semantics of relative and absolute gradable
  adjectives* (2007)][kennedy-2007]
-/

@[expose] public section

namespace Rett2015

open Degree
open English.Adjectives

/-! ### Polar (in)variance and markedness -/

/-- A construction is polar-invariant, in Rett's sense, when the two antonyms yield the same truth
conditions in it, so that the marked antonym has an unmarked competitor. Equatives and degree
questions are polar-invariant; positives, comparatives, and measure phrases are not. -/
def IsPolarInvariant : Construction → Prop
  | .equative | .degreeQuestion => True
  | .positive | .comparative | .measurePhrase => False

instance : DecidablePred IsPolarInvariant
  | .equative | .degreeQuestion => isTrue trivial
  | .positive | .comparative | .measurePhrase => isFalse id

/-- Negative antonyms are the marked members of their pairs. -/
def IsMarked (p : Polarity) : Prop := p = .negative

instance : DecidablePred IsMarked := fun p ↦ inferInstanceAs (Decidable (p = .negative))

/-! ### The implicature derivation -/

/-- Evaluativity is derived by a Quantity implicature (Chapter 3's degree tautology) or a Manner
implicature (Chapter 5's Marked Meaning Principle). -/
inductive Implicature where
  | quantity
  | manner
  deriving DecidableEq, Repr

/-- The implicature deriving evaluativity for a construction and antonym polarity, if any, is
Quantity for the positive construction with either antonym, and Manner, by the Marked Meaning
Principle, for the marked antonym of a polar-invariant construction. -/
def implicature (c : Construction) (p : Polarity) : Option Implicature :=
  if c = .positive then some .quantity
  else if IsPolarInvariant c ∧ IsMarked p then some .manner else none

/-- A construction–polarity pair is evaluative iff some implicature derives it. -/
def Evaluative (c : Construction) (p : Polarity) : Prop := implicature c p ≠ none

instance (c : Construction) (p : Polarity) : Decidable (Evaluative c p) :=
  inferInstanceAs (Decidable (_ ≠ _))

theorem implicature_eq_manner_iff (c : Construction) (p : Polarity) :
    implicature c p = some .manner ↔ IsPolarInvariant c ∧ IsMarked p := by
  cases c <;> cases p <;> decide

theorem implicature_eq_quantity_iff (c : Construction) (p : Polarity) :
    implicature c p = some .quantity ↔ c = .positive := by
  cases c <;> cases p <;> decide

theorem evaluative_iff (c : Construction) (p : Polarity) :
    Evaluative c p ↔ c = .positive ∨ (IsPolarInvariant c ∧ IsMarked p) := by
  cases c <;> cases p <;> decide

/-! ### The book's contrasts

Chapter 1's *How short is Adam?* and *Adam is as short as Doug* are evaluative; their
positive-antonym counterparts are not. -/

/-- The implicature deriving evaluativity for a fragment adjective in a construction, read off
its lexicalized polarity. -/
def evaluativity (a : GradableAdjective) (c : Construction) : Option Implicature :=
  implicature c a.polarity

theorem as_short_as : evaluativity short .equative = some .manner := rfl

theorem as_tall_as : evaluativity tall .equative = none := rfl

theorem how_short : evaluativity short .degreeQuestion = some .manner := rfl

/-! ### Polar variance grounded in the comparison semantics

[rett-2015] reduces polar (in)variance to mutual entailment of the antonyms' non-evaluative
readings: the strengthened ("exactly") equatives of the two antonyms share truth conditions,
so a truth-conditionally equivalent unmarked alternative exists and the Marked Meaning
Principle can fire; the antonym comparatives exclude each other, so no such alternative
exists. Degree questions pattern with the equative — both antonyms' true answers are the
subject's actual measure. -/

section PolarVarianceGrounding

variable {Entity D : Type*} [LinearOrder D] (μ : Entity → D) (a b : Entity) (p : Polarity)

theorem exact_equative_iff_eq :
    (a ∈ μ ⁻¹' (p • Comparison.ge).interval (μ b) ∧
      a ∉ μ ⁻¹' (p • Comparison.gt).interval (μ b)) ↔ μ a = μ b := by
  cases p <;> simp [eq_iff_le_not_lt, and_comm]

/-- The strengthened equatives of two antonyms, *exactly as tall as* and *exactly as short as*,
are mutually entailing. -/
theorem exact_equative_antonym_invariant :
    (a ∈ μ ⁻¹' (p • Comparison.ge).interval (μ b) ∧
        a ∉ μ ⁻¹' (p • Comparison.gt).interval (μ b)) ↔
      (a ∈ μ ⁻¹' ((Polarity.negative * p) • Comparison.ge).interval (μ b) ∧
        a ∉ μ ⁻¹' ((Polarity.negative * p) • Comparison.gt).interval (μ b)) := by
  rw [exact_equative_iff_eq, exact_equative_iff_eq]

theorem comparative_antonyms_exclusive (h : a ∈ μ ⁻¹' (p • Comparison.gt).interval (μ b)) :
    a ∉ μ ⁻¹' ((Polarity.negative * p) • Comparison.gt).interval (μ b) := by
  cases p <;> simpa using lt_asymm h

/-- Wherever the antonyms could differ, `μ a ≠ μ b`, their comparatives are complementary, so no
truth-conditionally equivalent unmarked alternative exists. -/
theorem comparative_antonym_variant (h : μ a ≠ μ b) :
    a ∈ μ ⁻¹' (p • Comparison.gt).interval (μ b) ↔
      a ∉ μ ⁻¹' ((Polarity.negative * p) • Comparison.gt).interval (μ b) := by
  cases p <;> simp [lt_iff_le_and_ne, h.symm, h]

end PolarVarianceGrounding

/-! ### Table 3.1 -/

/-- A Table 3.1 judgment records the construction, the antonym polarity, and whether the sentence is
evaluative. The ungrammatical negative-antonym measure phrase carries no judgment. -/
def datum (e : Datum) : Option (Construction × Polarity × Bool) :=
  do
    let c ← e.parse? "construction" [("positive", Construction.positive),
      ("comparative", .comparative), ("equative", .equative), ("measurePhrase", .measurePhrase),
      ("degreeQuestion", .degreeQuestion)]
    let p ← e.parse? "polarity" [("positive", Polarity.positive), ("negative", .negative)]
    let v ← e.parse? "evaluative" [("true", true), ("false", false)]
    pure (c, p, v)

/-- The Table 3.1 judgments. -/
def data : List (Construction × Polarity × Bool) := Examples.all.filterMap datum

/-- The predictions match every Table 3.1 judgment. -/
theorem evaluative_iff_observed : ∀ d ∈ data, Evaluative d.1 d.2.1 ↔ d.2.2 = true := by
  decide

end Rett2015
