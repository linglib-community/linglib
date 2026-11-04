module

public import Linglib.Core.Order.Hom.CompleteLattice
public import Linglib.Semantics.Degree.Quantifier
public import Linglib.Semantics.Degree.CresswellDegree
public import Linglib.Semantics.Quantification.Basic

/-!
# Hoeksema (1983): negative polarity and the comparative

This file formalizes Hoeksema's semantics for the two comparative constructions of English and
Dutch. The NP-comparative *taller than NP* sends a generalized quantifier `Q` to the individuals
`x` for which the set of individuals shorter than `x` belongs to `Q`. This map is a Boolean
homomorphism and [the only one](##PreservesOrdering.eq_npComparative) that gets the comparative
right on proper names, so it is monotone increasing and, by Ladusaw's criterion, [no environment
for negative polarity items](##not_antitone_npComparative). The S-comparative *taller than S* sends
a set of degrees to the individuals above all of them. It is anti-additive and hence [monotone
decreasing](##gtOverSet_antitone), so it licenses negative polarity items,
including the Dutch *ook maar*, which Zwarts's hypothesis restricts to anti-additive triggers.
The two comparatives coincide on a proper name and the singleton of its degree.

## Implementation notes

Degrees are values of a measure `μ`, and the grading relation `x > y` is `μ y < μ x`. This
[loses nothing](##gradingRelation_iff_exists_measure): a grading relation is exactly a relation read
off a measure into a linear order, and the classes of Definition 7 are [the values of the canonical
one](##mem_degree_iff), which are also the classes of Cresswell's construction. The results on the
NP-comparative need neither of the paper's conditions on grading relations (Definitions 1 and 2),
so `μ` takes values in a preorder. The homomorphism preserves arbitrary unions and intersections,
which Fact 2 needs on infinite domains (the paper's footnote 11). The S-comparative of Definition 8
is `(μ ⁻¹' strictUpperBounds ·)`, and its anti-additivity (Fact 5) is
`gtOverSet_isAntiAdditive`; on a disjunction this is what Cresswell's footnote 10 notes,
`Cresswell1976.erThan_union`.

## References

* [hoeksema-1983]
* [cresswell-1976]
* [ladusaw-1979]
* [zwarts-1998]
-/

@[expose] public section

namespace Hoeksema1983

open Quantifier CompleteLatticeHom

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

-- Fact 2, Fact 1
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

-- §3.9, (44)
theorem npComparative_individual (b : Entity) :
    npComparative μ (Quantifier.individual b) = μ ⁻¹' strictUpperBounds {μ b} := by
  ext a
  exact (npComparative_preservesOrdering μ a b).symm.trans (by simp)

/-! ### Grading relations and degrees (Definitions 1, 2, 7, 8) -/

section Degrees

universe u

variable {U : Type u} (gt : U → U → Prop) {a b x : U}

/-- The degree of `a` is what `a` neither exceeds nor is exceeded by (Definition 7). The paper's
degree is a function of an adjective's extension and relation, but does not use the extension. -/
def degree (a : U) : Set U := {x | ¬ gt x a ∧ ¬ gt a x}

variable {gt} in
-- Definition 3
theorem mem_npComparative_iff {D : Type*} [Preorder D] {μ : U → D}
    (h : ∀ x y, gt x y ↔ μ y < μ x) (Q : Set (Set U)) (x : U) :
    x ∈ npComparative μ Q ↔ {y | gt x y} ∈ Q := by
  have : {y | gt x y} = μ ⁻¹' Set.Iio (μ x) := Set.ext fun y ↦ h x y
  rw [this]
  exact Iff.rfl

attribute [local instance] isStrictWeakOrder_of_isOrderConnected

variable [IsOrderConnected U gt] [Std.Asymm gt]

-- p. 411: "Other properties of comparatives, like transitivity, can be shown to follow".
example : IsTrans U gt := inferInstance

/-- On a grading relation the degree of `a` is its class in Cresswell's construction, though the
paper sets its definition against his pair of a point and a relation (n. 15). -/
theorem mem_degree_iff : x ∈ degree gt a ↔ (⟦x⟧ : CresswellDegree gt) = ⟦a⟧ :=
  cresswellSetoid_iff_incompRel.symm.trans Quotient.eq.symm

-- p. 424
theorem degree_eq_degree_iff : degree gt a = degree gt b ↔ ¬ gt a b ∧ ¬ gt b a := by
  refine ⟨fun h ↦ (h ▸ (mem_degree_iff gt).2 rfl : a ∈ degree gt b), fun h ↦ Set.ext fun x ↦ ?_⟩
  rw [mem_degree_iff, mem_degree_iff, (mem_degree_iff gt).1 h]

-- p. 424, Definition 8 on the degrees of `a` and `b`, ordered by `d_x > d_y` iff `x > y`, which
-- Cresswell's (4.2) shows consistent.
theorem mk_preimage_strictUpperBounds_pair [DecidableRel gt] :
    Quotient.mk (cresswellSetoid gt) ⁻¹' strictUpperBounds {⟦a⟧, ⟦b⟧} = {x | gt x a ∧ gt x b} := by
  ext x
  simp [strictUpperBounds]

variable {gt}

omit [IsOrderConnected U gt] [Std.Asymm gt] in
/-- A relation is a grading relation, almost connected and asymmetric (Definitions 1 and 2), exactly
when it is read off a measure into a linear order, the classes of Definition 7 giving the canonical
one. -/
theorem gradingRelation_iff_exists_measure :
    (IsOrderConnected U gt ∧ Std.Asymm gt) ↔
      ∃ (D : Type u) (_ : LinearOrder D) (μ : U → D), ∀ x y, gt x y ↔ μ y < μ x := by
  refine ⟨fun ⟨_, _⟩ ↦ ?_, fun ⟨D, _, μ, h⟩ ↦
    ⟨⟨fun x z y hxy ↦ ?_⟩, ⟨fun x y hxy hyx ↦ lt_asymm ((h _ _).1 hxy) ((h _ _).1 hyx)⟩⟩⟩
  · classical
    exact ⟨CresswellDegree gt, inferInstance, Quotient.mk _, fun _ _ ↦ Iff.rfl⟩
  · exact (lt_or_ge (μ z) (μ x)).elim (.inl <| (h _ _).2 ·)
      fun hz ↦ .inr <| (h _ _).2 <| ((h _ _).1 hxy).trans_le hz

-- A third thing incommensurable with two compared ones breaks almost-connectedness, so no measure
-- reads the relation off.
example : ¬ ∃ (D : Type) (_ : LinearOrder D) (μ : Fin 3 → D),
    ∀ x y, (x = 1 ∧ y = 0) ↔ μ y < μ x := fun h ↦
  absurd ((gradingRelation_iff_exists_measure.2 h).1.conn 1 2 0 ⟨rfl, rfl⟩) (by decide)

end Degrees

/-! ### Triggers of *ook maar* -/

/-- The two Dutchmen of the §4.1 model, Jan and Piet. -/
inductive Dutchman where
  | jan
  | piet

/-- The quantifier *niet iedere Nederlander* 'not every Dutchman' holds of a property that some
Dutchman lacks. -/
def notEveryDutchman : Set Dutchman → Prop :=
  fun P ↦ ¬ Det.every Set.univ P

-- (51), (45b), §4.1
theorem not_isAntiAdditive_notEveryDutchman : ¬ IsAntiAdditive notEveryDutchman := by
  rw [Quantifier.isAntiAdditive_iff]
  intro h
  refine (h {.jan} {.piet}).2 ⟨fun h ↦ ?_, fun h ↦ ?_⟩ fun x _ ↦ ?_
  · simpa using h (Set.mem_univ .piet)
  · simpa using h (Set.mem_univ .jan)
  · cases x <;> simp

end Hoeksema1983
