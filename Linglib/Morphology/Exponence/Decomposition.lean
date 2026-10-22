module

public import Linglib.Morphology.Exponence.Select
public import Mathlib.Data.Finset.Card

/-!
# Feature-decomposition exponence and the Subset Principle

In privative feature-decomposition accounts of syncretism, as Caha's and Bobaljik's, each cell
is decomposed into a set of features `D : Cell → Finset K`, and a rule applies where its feature
specification is contained in the cell's, the Subset Principle. Competition is Halle's feature
counting, the applicable rule of greatest specification winning. Specifications ordered by
inclusion need not be nested, so counting is specificity only when the applicable specifications
are; the linear containment engine is the chain decomposition `Finset.Iic`
(`Containment.pattern_toDecomposition`).

## Main definitions

* `Decomposition.Rule`: a feature specification with an exponent.
* `Decomposition.pattern`: the exponent at each cell of the applicable rule with the most
  features.
* `Decomposition.IsWinner`: strict feature-count competition.

## Main results

* `Decomposition.noABA`: a cell nested between two others is realized by any rule winning both.

## References

* [bobaljik-2012]
* [caha-2009]
* [halle-1997]
-/

@[expose] public section

namespace Morphology.Decomposition

open Morphology Morphology.Exponence

variable {K : Type*}

/-- A rule of exponence over a feature decomposition `D` pairs a feature specification with an
exponent. It applies where its features are a subset of the cell's, the **Subset Principle**
([halle-1997]). -/
structure Rule (Cell : Type*) (D : Cell → Finset K) (F : Type*) where
  /-- The rule's feature specification. -/
  feats : Finset K
  /-- The exponent inserted. -/
  exponent : F
  deriving DecidableEq

variable {Cell F : Type*} {D : Cell → Finset K}

instance : Exponence.Rule (Rule Cell D F) Cell F :=
  ⟨Rule.exponent, fun r c ↦ r.feats ⊆ D c⟩

@[simp] theorem applies_iff {r : Rule Cell D F} {c : Cell} :
    Exponence.Applies r c ↔ r.feats ⊆ D c := Iff.rfl

/-- In strict competition `r` beats every other applicable rule on feature cardinality. -/
def IsWinner (v : RuleSet (Rule Cell D F)) (c : Cell) (r : Rule Cell D F) : Prop :=
  r ∈ v ∧ r.feats ⊆ D c ∧
    ∀ s ∈ v, s.feats ⊆ D c → s ≠ r → s.feats.card < r.feats.card

variable [DecidableEq K]

instance : DecidableRel (Exponence.Applies : Rule Cell D F → Cell → Prop) :=
  fun r c ↦ inferInstanceAs (Decidable (r.feats ⊆ D c))

/-- The surface pattern of a rule set is, at each cell, the exponent of the most highly
specified applicable rule, the Elsewhere Principle as `selectBy` on feature cardinality
([halle-1997]'s counting formulation). -/
def pattern (v : RuleSet (Rule Cell D F)) (c : Cell) : Option F :=
  (v.selectBy (fun r : Rule Cell D F ↦ r.feats.card) c).map Rule.exponent

/-- When the middle cell `y` nests between the outer cells, with `D y ⊆ D z` (appliers at `y`
persist to `z`) and `D x ∩ D z ⊆ D y` (appliers at both outer cells reach `y`), a rule winning
both `x` and `z` also wins `y`, so no exponent can interrupt an A_A pattern with a distinct
middle B. This is *ABA order-theoretically. The hypotheses are the shared profile of Strong and
Weak Case Containment, and No Case Containment violates the first. -/
theorem noABA {v : RuleSet (Rule Cell D F)} {A B : Rule Cell D F} {x y z : Cell}
    (h1 : D y ⊆ D z) (h2 : D x ∩ D z ⊆ D y)
    (hx : IsWinner v x A) (hz : IsWinner v z A) (hy : IsWinner v y B) : B = A := by
  by_contra hne
  have hAy : A.feats ⊆ D y := fun k hk ↦
    h2 (Finset.mem_inter.mpr ⟨hx.2.1 hk, hz.2.1 hk⟩)
  have hAB : A.feats.card < B.feats.card :=
    hy.2.2 A hx.1 hAy (fun h ↦ hne h.symm)
  have hBz : B.feats ⊆ D z := fun k hk ↦ h1 (hy.2.1 hk)
  exact absurd (hz.2.2 B hy.1 hBz hne) (Nat.lt_asymm hAB)

end Morphology.Decomposition
