module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Sprouse, Wagers and Phillips (2012): A Test of the Relation Between Working-Memory Capacity and Syntactic Island Effects

This file formalizes the logic of [sprouse-et-al-2012]'s test of the resource-limitation
theory of island effects. An island effect is defined factorially, over the four sentences
that cross the presence of an island structure with the position of the gap: it is the
superadditive interaction, the drop in acceptability from combining a long-distance
dependency with an island structure exceeding the sum of the drops for each alone, and it is
measured by the differences-in-differences score (`dd`, `superadditive_iff_dd_pos`). The
simplest reductionist theory, on which a dependency cost and a structure cost add, predicts
additivity and so no island effect (`dd_linear`). The resource-limitation theory of
[kluender-kutas-1993] adds an overload penalty when the two processes, deployed
simultaneously, exceed a limited capacity, so its interaction is the penalty
(`dd_resourceLimitation`), decreasing in capacity and vanishing once capacity suffices
(`dd_resourceLimitation_antitone`, `dd_resourceLimitation_eq_zero`); a grammatical theory
penalizes the island-violating sentence alone, so its interaction is the constraint's penalty
whatever the capacity (`dd_grammatical`). The two theories part on whether the interaction
covaries with working-memory capacity across speakers, the prediction the paper tests.

## Implementation notes

Ratings are values in an ordered field, one per cell of the design, as for a speaker's mean
ratings; the score of the paper's (8) is the interaction contrast, and the linking hypothesis
that costs lower acceptability is the sign convention of the models. The overload penalty is
any function of capacity, with the theory's assumptions, that it is nonnegative, decreasing
in capacity, and zero when capacity covers both costs, as hypotheses. The two experiments,
over three hundred speakers on four island types, with seven-point and magnitude-estimation
ratings and serial-recall and n-back measures of capacity, found no relation between
capacity and the interaction and no structure cost for complex NP and subject islands; the
results and their resampling analyses are not formalized.

## References

* [sprouse-et-al-2012]
* [kluender-kutas-1993]
* [hofmeister-sag-2010]
* [sprouse-2007]
-/

@[expose] public section

namespace SprouseEtAl2012

/-- The structure factor: whether the sentence contains an island structure. -/
inductive Structure
  | nonisland | island
  deriving DecidableEq, Repr

/-- The gap-position factor: whether the dependency ends in the matrix clause or in the
embedded clause. -/
inductive GapPosition
  | matrix | embedded
  deriving DecidableEq, Repr

/-- The ratings of a 2 × 2 factorial design (the paper's (5)): one rating per structure and gap
position. -/
abbrev Ratings (α : Type*) := Structure → GapPosition → α

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- The dependency-length effect: the drop from a matrix to an embedded gap in nonisland
structures. -/
def lengthEffect (r : Ratings α) : α := r .nonisland .matrix - r .nonisland .embedded

/-- The island-structure effect: the drop from a nonisland to an island structure with a
matrix gap. -/
def structureEffect (r : Ratings α) : α := r .nonisland .matrix - r .island .matrix

/-- The differences-in-differences score (the paper's (8)): the island-structure drop with an
embedded gap less the island-structure drop with a matrix gap. -/
def dd (r : Ratings α) : α :=
  (r .nonisland .embedded - r .island .embedded) - (r .nonisland .matrix - r .island .matrix)

/-- Additivity: the drop for the island-violating sentence is the sum of the two effects. -/
def Additive (r : Ratings α) : Prop :=
  lengthEffect r + structureEffect r = r .nonisland .matrix - r .island .embedded

/-- Superadditivity, the island effect: the drop for the island-violating sentence exceeds the
sum of the two effects. -/
def Superadditive (r : Ratings α) : Prop :=
  lengthEffect r + structureEffect r < r .nonisland .matrix - r .island .embedded

theorem additive_iff_dd_eq_zero (r : Ratings α) : Additive r ↔ dd r = 0 := by
  unfold Additive lengthEffect structureEffect dd
  constructor <;> intro h <;> linarith

theorem superadditive_iff_dd_pos (r : Ratings α) : Superadditive r ↔ 0 < dd r := by
  unfold Superadditive lengthEffect structureEffect dd
  constructor <;> intro h <;> linarith

/-! ### The theories -/

/-- The simplest reductionist theory (the paper's (4)): a baseline lowered by the cost of a
long-distance dependency and the cost of an island structure, each charged wherever
present. -/
def linear (base c₁ c₂ : α) : Ratings α := λ s g =>
  base - (if g = .embedded then c₁ else 0) - (if s = .island then c₂ else 0)

/-- The resource-limitation theory (the paper's (6)): the linear costs, and an overload
penalty depending on capacity in the sentence deploying both processes at once. -/
def resourceLimitation (base c₁ c₂ : α) (overload : α → α) (capacity : α) : Ratings α :=
  λ s g => linear base c₁ c₂ s g -
    (if s = .island ∧ g = .embedded then overload capacity else 0)

/-- A grammatical theory: the linear costs, and a constraint penalty on the island-violating
sentence alone. -/
def grammatical (base c₁ c₂ penalty : α) : Ratings α :=
  λ s g => linear base c₁ c₂ s g - (if s = .island ∧ g = .embedded then penalty else 0)

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem lengthEffect_linear (base c₁ c₂ : α) : lengthEffect (linear base c₁ c₂) = c₁ := by
  simp [lengthEffect, linear]

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem structureEffect_linear (base c₁ c₂ : α) :
    structureEffect (linear base c₁ c₂) = c₂ := by
  simp [structureEffect, linear]

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem dd_linear (base c₁ c₂ : α) : dd (linear base c₁ c₂) = 0 := by
  simp [dd, linear]

theorem additive_linear (base c₁ c₂ : α) : Additive (linear base c₁ c₂) :=
  (additive_iff_dd_eq_zero _).2 (dd_linear base c₁ c₂)

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem dd_resourceLimitation (base c₁ c₂ : α) (overload : α → α) (capacity : α) :
    dd (resourceLimitation base c₁ c₂ overload capacity) = overload capacity := by
  simp [dd, resourceLimitation, linear]
  ring

theorem superadditive_resourceLimitation_iff (base c₁ c₂ : α) (overload : α → α)
    (capacity : α) :
    Superadditive (resourceLimitation base c₁ c₂ overload capacity) ↔ 0 < overload capacity := by
  rw [superadditive_iff_dd_pos, dd_resourceLimitation]

omit [IsStrictOrderedRing α] in
/-- Limited capacity: with a penalty decreasing in capacity, the island effect decreases as
capacity grows, the prediction of the paper's Figure 2a. -/
theorem dd_resourceLimitation_antitone (base c₁ c₂ : α) {overload : α → α}
    (h : Antitone overload) :
    Antitone λ capacity => dd (resourceLimitation base c₁ c₂ overload capacity) := by
  simpa only [dd_resourceLimitation] using h

omit [IsStrictOrderedRing α] in
theorem dd_resourceLimitation_eq_zero (base c₁ c₂ : α) {overload : α → α}
    (h : ∀ capacity, c₁ + c₂ ≤ capacity → overload capacity = 0) {capacity : α}
    (hc : c₁ + c₂ ≤ capacity) : dd (resourceLimitation base c₁ c₂ overload capacity) = 0 := by
  rw [dd_resourceLimitation, h capacity hc]

omit [LinearOrder α] [IsStrictOrderedRing α] in
/-- The interaction under a grammatical theory is the constraint's penalty, the same at every
capacity, the prediction of the paper's Figure 2b. -/
theorem dd_grammatical (base c₁ c₂ penalty : α) :
    dd (grammatical base c₁ c₂ penalty) = penalty := by
  simp [dd, grammatical, linear]
  ring

omit [LinearOrder α] [IsStrictOrderedRing α] in
theorem resourceLimitation_eq_grammatical (base c₁ c₂ : α) (overload : α → α) (capacity : α) :
    resourceLimitation base c₁ c₂ overload capacity =
      grammatical base c₁ c₂ (overload capacity) :=
  rfl

end SprouseEtAl2012
