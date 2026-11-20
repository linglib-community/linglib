module

public import Linglib.Data.Examples.Rett2020b
public import Linglib.Semantics.Degree.Quantifier

/-!
# Rett (2020): Separate but equal: a typology of equative constructions

An equative of a gradable adjective relates the set `S` of degrees its standard of comparison
reaches to the set `T` of degrees its target reaches; for an adjective with measure `μ`, a target
`a` and a standard `b` these are `Set.Iic (μ b)` and `Set.Iic (μ a)`. We define the four classes
of equative constructions that the chapter distinguishes by their truth conditions,
`Class.Holds`. A predicative equative, formed with a word for *equal*, holds when `T = S`. A
sufficientive equative, English *as … as*, is the degree quantifier `S ⊆ T`. A demonstrative
equative, Italian *tanto … quanto*, says that the greatest degree of `S` is in `T`,
`Quantifier.MaxIn T S`. An implicit equative, one with no parameter marker, holds when `T` and
`S` both contain a degree above a contextual standard `s`.

A demonstrative equative holds exactly when the standard has a greatest degree and the
sufficientive equative holds, `holds_demonstrative_iff`, so on a measure both are `μ b ≤ μ a`.
A class has a weak reading, `Class.HasWeakReading`, when its equative holds of some target that
exceeds its standard, and it is evaluative, `Class.Evaluative`, when its equative entails that the
target exceeds `s`. Every class but the predicative one has a weak reading, `hasWeakReading_iff`,
and the implicit class alone is evaluative, `evaluative_iff`. The examples that continue an
equative with *in fact she's taller* are acceptable exactly in the classes with a weak reading,
`acceptable_iff_hasWeakReading`, and those that continue it with *but she's short* exactly in the
classes that are not evaluative, `acceptable_iff_not_evaluative`.

## Implementation notes

The truth conditions are stated on sets of degrees, the type of the chapter's degree
quantifiers, and not on measures, since the sufficientive and the demonstrative equative differ
only on a standard with no greatest degree. The implicit equative of the chapter also closes
existentially over a property that the two clauses share; it constrains nothing and is left out,
so that the implicit equative is the conjunction of two positive forms. The chapter derives it
for the relatives with only a standard marker and classes the conjoined equatives with them.

That a factor modifier such as *twice* is acceptable only in a sufficientive equative is the
chapter's claim that only a sufficientive parameter marker is a degree quantifier. It does not
follow from the truth conditions, which a factor could scale in every class, and
`acceptable_iff_eq_sufficientive` checks it against the examples as stated.

The strategies with a case-marked standard or with dedicated morphemes have no class. Slovenian
has no row for the diagnostics the chapter records no judgment on, and neither has (60), which
the chapter prints without a judgment.

## References

* [J. Rett, *Separate but equal: a typology of equative constructions* (2020)][rett-2020b]
* [J. Rett, *The semantics of evaluativity* (2015)][rett-2015b]
* [C. Kennedy, *Modes of comparison* (2007)][kennedy-2007a]
-/

@[expose] public section

open Set

namespace Rett2020b

open Examples (Example Strategy Diagnostic)

/-! ### Classes -/

/-- Figure 3: the theoretical classes of equatives. -/
inductive Class where
  /-- The equatives formed with a predicate or an adverbial meaning *equal*. -/
  | predicative
  /-- The explicit equatives whose parameter marker is a sufficientive, a degree quantifier. -/
  | sufficientive
  /-- The explicit equatives whose parameter marker is a degree demonstrative. -/
  | demonstrative
  /-- The equatives that are not predicative and do not mark their parameter. -/
  | implicit
  deriving DecidableEq, Fintype

/-- Figure 3: the class of a strategy, where the chapter assigns one. -/
def Examples.Strategy.class? : Strategy → Option Class
  | .smOnly | .conjoined => some .implicit
  | .demonstrative => some .demonstrative
  | .sufficientive => some .sufficientive
  | .predicateMain | .predicateAdverbial => some .predicative
  | .dedicated => none

/-- The class of the strategy of an example. -/
def Examples.Example.class? (x : Example) : Option Class := x.strategy.bind (·.class?)

/-! ### Truth conditions -/

variable {D : Type*} [LinearOrder D] {s x y : D} {S T : Set D} {c : Class}

/-- The truth conditions of an equative of each class, for the degrees `S` of the standard of
comparison, the degrees `T` of the target and a contextual standard `s`: the lexical equality of
a predicative equative, the set-based *as* of (5b), the demonstrative equative of (86) and the
two evaluative clauses of (81). -/
def Class.Holds (s : D) : Class → Set D → Set D → Prop
  | .predicative, S, T => T = S
  | .sufficientive, S, T => S ⊆ T
  | .demonstrative, S, T => Quantifier.MaxIn T S
  | .implicit, S, T => (T ∩ Ioi s).Nonempty ∧ (S ∩ Ioi s).Nonempty

/-- A demonstrative equative holds exactly when the standard has a greatest degree and the
sufficientive equative holds. -/
theorem holds_demonstrative_iff (hT : IsLowerSet T) :
    Class.demonstrative.Holds s S T ↔ (∃ m, IsGreatest S m) ∧ Class.sufficientive.Holds s S T :=
  ⟨fun ⟨m, hm, h⟩ ↦ ⟨⟨m, h⟩, fun _ hd ↦ hT (h.2 hd) hm⟩, fun ⟨⟨m, h⟩, hST⟩ ↦ ⟨m, hST h.1, h⟩⟩

@[simp]
theorem holds_predicative_Iic : Class.predicative.Holds s (Iic y) (Iic x) ↔ x = y := Iic_inj

@[simp]
theorem holds_sufficientive_Iic : Class.sufficientive.Holds s (Iic y) (Iic x) ↔ y ≤ x :=
  Iic_subset_Iic

@[simp]
theorem holds_demonstrative_Iic : Class.demonstrative.Holds s (Iic y) (Iic x) ↔ y ≤ x :=
  Quantifier.maxIn_Iic

@[simp]
theorem holds_implicit_Iic : Class.implicit.Holds s (Iic y) (Iic x) ↔ s < x ∧ s < y := by
  simp [Class.Holds, Iic_inter_Ioi]

/-! ### Weak readings and evaluativity -/

variable (D) in
/-- A class has a weak reading when its equative holds of some target that exceeds its
standard. -/
def Class.HasWeakReading (c : Class) : Prop := ∃ s x y : D, y < x ∧ c.Holds s (Iic y) (Iic x)

variable (D) in
/-- A class is evaluative when its equative entails that the target exceeds the contextual
standard. -/
def Class.Evaluative (c : Class) : Prop := ∀ s x y : D, c.Holds s (Iic y) (Iic x) → s < x

/-- Every class but the predicative one has a weak reading. -/
theorem hasWeakReading_iff [Nonempty D] [NoMaxOrder D] :
    c.HasWeakReading D ↔ c ≠ .predicative := by
  obtain ⟨s⟩ := ‹Nonempty D›
  obtain ⟨y, hy⟩ := exists_gt s
  obtain ⟨x, hx⟩ := exists_gt y
  cases c
  · simp [Class.HasWeakReading]
  · simpa [Class.HasWeakReading] using ⟨x, y, hx, hx.le⟩
  · simpa [Class.HasWeakReading] using ⟨x, y, hx, hx.le⟩
  · simpa [Class.HasWeakReading] using ⟨s, x, y, hx, hy.trans hx, hy⟩

/-- The implicit class alone is evaluative. -/
theorem evaluative_iff [Nonempty D] : c.Evaluative D ↔ c = .implicit := by
  obtain ⟨d⟩ := ‹Nonempty D›
  cases c
  · exact iff_of_false (fun h ↦ lt_irrefl d (h d d d (holds_predicative_Iic.2 rfl))) (by decide)
  · exact iff_of_false (fun h ↦ lt_irrefl d (h d d d (holds_sufficientive_Iic.2 le_rfl)))
      (by decide)
  · exact iff_of_false (fun h ↦ lt_irrefl d (h d d d (holds_demonstrative_Iic.2 le_rfl)))
      (by decide)
  · exact iff_of_true (fun _ _ _ h ↦ (holds_implicit_Iic.1 h).1) rfl

/-! ### The chapter's examples -/

variable (D) [Nonempty D]

/-- An equative continued by *in fact she's taller* is acceptable exactly when its class has a
weak reading. -/
theorem acceptable_iff_hasWeakReading [NoMaxOrder D] : ∀ x : Example, x.diagnostic = some .weak →
    ∀ c ∈ x.class?, (x.datum.judgment = .acceptable ↔ c.HasWeakReading D) := by
  simp only [hasWeakReading_iff]
  decide

/-- An equative continued by *but she's short* is acceptable exactly when its class is not
evaluative. -/
theorem acceptable_iff_not_evaluative : ∀ x : Example, x.diagnostic = some .evaluativity →
    ∀ c ∈ x.class?, (x.datum.judgment = .acceptable ↔ ¬ c.Evaluative D) := by
  simp only [evaluative_iff]
  decide

-- (54), (59), (62), (64), (67), (72), (75)
theorem acceptable_iff_eq_sufficientive : ∀ x : Example, x.diagnostic = some .factor →
    ∀ c ∈ x.class?, (x.datum.judgment = .acceptable ↔ c = .sufficientive) := by
  decide

-- Figure 3
theorem exists_class_diagnostic :
    ∀ (c : Class) (d : Diagnostic), ∃ x : Example, x.class? = some c ∧ x.diagnostic = some d := by
  decide

end Rett2020b
