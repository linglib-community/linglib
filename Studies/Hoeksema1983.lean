module

public import Linglib.Core.Order.Hom.CompleteLattice
public import Linglib.Semantics.Quantification.Signatures
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Quantification.Basic

/-!
# Hoeksema (1983): negative polarity and the comparative

This file formalizes Hoeksema's semantics for the two comparative constructions of English and
Dutch. The NP-comparative *taller than NP* sends a generalized quantifier `Q` to the individuals
`x` for which the set of individuals shorter than `x` belongs to `Q`. This map is a Boolean
homomorphism and the only one that gets the comparative right on proper names, so it is
monotone increasing and, by Ladusaw's criterion, no environment for negative polarity items.
The S-comparative *taller than S* sends a set of degrees to the individuals above all of them.
It is anti-additive and hence monotone decreasing, so it licenses negative polarity items,
including the Dutch *ook maar*, which Zwarts's hypothesis restricts to anti-additive triggers.
The two comparatives coincide on a proper name and the singleton of its degree.

## Main definitions

* `npComparative`: the NP-comparative as a complete lattice homomorphism (Definition 3).
* `PreservesOrdering`: a map from quantifiers to predicates respects the grading relation on
  proper names (Definition 4).

## Implementation notes

Degrees are values of a measure `μ` in a preorder rather than the equivalence classes of
Definition 7, and the grading relation `x > y` is `μ y < μ x`. The results on the
NP-comparative need neither of the paper's conditions on grading relations (Definitions 1
and 2). The homomorphism preserves arbitrary unions and intersections, which Fact 2 needs on
infinite domains (the paper's footnote 11). The S-comparative of Definition 8 is
`(μ ⁻¹' strictUpperBounds ·)`, and its anti-additivity (Fact 5) is
`Degree.gtOverSet_isAntiAdditive`.

## References

* [hoeksema-1983]
* [ladusaw-1979]
* [zwarts-1998]
-/

@[expose] public section

namespace Hoeksema1983

open Degree NaturalLogic Quantifier CompleteLatticeHom

variable {Entity D : Type*} [Preorder D] (μ : Entity → D)

/-! ### The NP-comparative -/

/-- The NP-comparative of Definition 3 holds of `x` and a quantifier `Q` when the individuals
below `x` on the scale `μ` form a set in `Q`. As a preimage map it preserves intersections,
unions and complements, which is (22). -/
def npComparative : CompleteLatticeHom (Set (Set Entity)) (Set Entity) :=
  setPreimage fun x ↦ μ ⁻¹' Set.Iio (μ x)

-- Fact 3
theorem npComparative_monotone : Monotone (npComparative μ) :=
  OrderHomClass.mono _

/-- On a nonempty domain the NP-comparative is not monotone decreasing, so by Ladusaw's
criterion it is not a negative polarity environment (§3.6). -/
theorem not_antitone_npComparative [Nonempty Entity] : ¬ Antitone (npComparative μ) := by
  intro h
  have := h (bot_le : (⊥ : Set (Set Entity)) ≤ ⊤)
  rw [map_top, map_bot] at this
  exact this (Set.mem_univ (Classical.arbitrary Entity))

/-! ### Uniqueness -/

/-- A map `f` from quantifiers to predicates preserves the ordering (Definition 4) when `a > b`
holds exactly when `a` falls under `f` of the quantifier that the name of `b` denotes. -/
def PreservesOrdering (f : Set (Set Entity) → Set Entity) : Prop :=
  ∀ a b, μ b < μ a ↔ a ∈ f (Quantifier.individual b)

-- (30)
theorem npComparative_preservesOrdering : PreservesOrdering μ (npComparative μ) :=
  fun _ _ ↦ Iff.rfl

variable {μ}

-- Fact 1
theorem PreservesOrdering.apply_individual {f g : Set (Set Entity) → Set Entity}
    (hf : PreservesOrdering μ f) (hg : PreservesOrdering μ g) (b : Entity) :
    f (Quantifier.individual b) = g (Quantifier.individual b) :=
  Set.ext fun a ↦ (hf a b).symm.trans (hg a b)

/-- Two ordering-preserving homomorphisms from quantifiers to predicates are equal (Fact 2), each
being the preimage map that Fact 1 determines. -/
theorem PreservesOrdering.eq {f g : CompleteLatticeHom (Set (Set Entity)) (Set Entity)}
    (hf : PreservesOrdering μ f) (hg : PreservesOrdering μ g) : f = g := by
  obtain ⟨φ, rfl⟩ := setPreimage_surjective f
  obtain ⟨ψ, rfl⟩ := setPreimage_surjective g
  exact congrArg setPreimage <| funext fun x ↦ Set.ext fun b ↦
    Set.ext_iff.1 (hf.apply_individual hg b) x

/-- The NP-comparative is the only homomorphism from quantifiers to predicates that preserves
the ordering (§3.5). -/
theorem PreservesOrdering.eq_npComparative
    {f : CompleteLatticeHom (Set (Set Entity)) (Set Entity)} (hf : PreservesOrdering μ f) :
    f = npComparative μ :=
  hf.eq (npComparative_preservesOrdering μ)

variable (μ)

/-! ### The S-comparative -/

/-- The S-comparative is monotone decreasing in its set of degrees (§3.8), since it is
anti-additive (Fact 5) and anti-additive maps are monotone decreasing (Fact 4). -/
theorem gtOverSet_antitone : Antitone (μ ⁻¹' strictUpperBounds ·) :=
  (gtOverSet_isAntiAdditive μ).antitone

/-- The NP-comparative of a proper name is the S-comparative of its degree's singleton (§3.9), as in
(44). -/
theorem npComparative_individual (b : Entity) :
    npComparative μ (Quantifier.individual b) = μ ⁻¹' strictUpperBounds {μ b} := by
  ext a
  exact (npComparative_preservesOrdering μ a b).symm.trans (by simp)

/-! ### Triggers of *ook maar* -/

/-- The two Dutchmen of the §4.1 model, Jan and Piet. -/
inductive Dutchman where
  | jan
  | piet

/-- The quantifier *niet iedere Nederlander* 'not every Dutchman' holds of a property that some
Dutchman lacks. -/
def notEveryDutchman : Set Dutchman → Prop :=
  fun P ↦ ¬ Det.every Set.univ P

/-- In the model (51), *niet iedere Nederlander* is not anti-additive, so by Zwarts's hypothesis it
cannot trigger *ook maar* (45b) (§4.1). -/
theorem not_isAntiAdditive_notEveryDutchman : ¬ IsAntiAdditive notEveryDutchman := by
  rw [Quantifier.isAntiAdditive_iff]
  intro h
  refine (h {.jan} {.piet}).2 ⟨fun h ↦ ?_, fun h ↦ ?_⟩ fun x _ ↦ ?_
  · simpa using h (Set.mem_univ .piet)
  · simpa using h (Set.mem_univ .jan)
  · cases x <;> simp

end Hoeksema1983
