/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.Soundness
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Bounds.Basic

/-!
# Completeness of the projectivity calculus

This file proves the converses to `Logic/Natural/Soundness.lean`: the
join and projection tables are tight, the seven relations are exactly
the nondegenerately realizable conjunctions of constraint atoms, and
the refinement order on signatures coincides with inclusion of
function classes.

Tightness ([icard-2012]'s Lemma 1.5, as an equality) has countermodels
already on the three-atom Boolean algebra `Finset (Fin 3)`. The
classification is [maccartney-manning-2009] §2's sixteen-class
partition, following Sánchez Valencia: the nine subsets outside the
range of `Relation.constraints` force an argument to `⊥` or `⊤` in
every bounded lattice.

## Main declarations

* `Relation.isLeast_join`, `Relation.join_le_iff`: each join cell is
  the least sound chaining ([icard-2012] Definition 1.4).
* `Relation.mem_range_constraints_of_holds`: a constraint set realized
  by a nondegenerate pair is one of the seven.
* `Relation.mem_range_constraints_iff`: the classification, as an iff
  against realizability on `Finset (Fin 3)`.
* `Relation.exists_isLeast_holds`: [icard-2012]'s Lemma 1.3 — any
  nondegenerate pair stands in a strongest relation — on any bounded
  lattice.
* `Signature.isLeast_project`: each projection cell is the least
  relation sound for the signature's function class ([icard-2012]
  Definition 2.3), with countermodels on the two-element Boolean
  algebra.
* `Signature.le_iff_holdsFor`: the refinement order is inclusion of
  function classes — [icard-2012]'s semantic definition of ≼,
  recovered.
* `Signature.isLeast_compose`, `Signature.holdsFor_comp`: composition
  is the least signature covering composites ([icard-2012]
  Definition 2.6).

## Implementation notes

The nine signatures are not an exhaustive classification of realizable
property profiles: the constant-`⊤` function is simultaneously
monotone, antitone, completely additive, and completely
anti-multiplicative, and `{+, −, ⊕, ⊟}` is no signature's property
set. The signatures are the downward-closed profiles [icard-2012]
names, each tight for its own row.

## References

* [icard-2012] — Definitions 1.4, 2.3, and 2.6, Lemmas 1.3, 1.5,
  and 2.4.
* [maccartney-manning-2009] — §2's sixteen-class partition, following
  Sánchez Valencia.
-/

@[expose] public section

namespace NaturalLogic

/-! ### Tightness of the join table -/

/-- **Tightness of the join table** ([icard-2012] Lemma 1.5 is an
equality): `R.join S` is the least — strongest — relation sound for
chaining `R` then `S`, already over the three-atom Boolean algebra.
Soundness over any bounded distributive lattice is
`Relation.Holds.join`; conversely any `T` sound on `Finset (Fin 3)`
alone weakens the table entry. -/
theorem Relation.isLeast_join (R S : Relation) :
    IsLeast {T : Relation | ∀ x y z : Finset (Fin 3),
      R.Holds x y → S.Holds y z → T.Holds x z} (R.join S) := by
  refine ⟨λ x y z hR hS => hR.join hS, λ T hT => ?_⟩
  by_contra hle
  have h : ∀ R S T : Relation, ¬ R.join S ≤ T →
      ∃ x y z : Finset (Fin 3), R.Holds x y ∧ S.Holds y z ∧ ¬ T.Holds x z := by
    decide
  obtain ⟨x, y, z, hR, hS, hT'⟩ := h R S T hle
  exact hT' (hT x y z hR hS)

/-! ### Why seven relations -/

theorem Relation.mem_range_constraints_of_holds {α : Type*} [Lattice α]
    [BoundedOrder α] {s : Finset Relation.Atom} {x y : α}
    (h : ∀ a ∈ s, a.Holds x y) (hx : x ≠ ⊥) (hx' : x ≠ ⊤)
    (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    s ∈ Set.range Relation.constraints := by
  by_contra hs
  have key : ∀ s : Finset Relation.Atom, (¬ ∃ R : Relation, R.constraints = s) →
      ({.le, .disjoint} ⊆ s ∨ {.le, .codisjoint} ⊆ s ∨
       {.ge, .disjoint} ⊆ s ∨ {.ge, .codisjoint} ⊆ s) := by decide
  rcases key s (λ ⟨R, hR⟩ => hs ⟨R, hR⟩) with hp | hp | hp | hp
  · exact hx ((h .disjoint (hp (by decide))).eq_bot_of_le (h .le (hp (by decide))))
  · exact hy' ((h .codisjoint (hp (by decide))).eq_top_of_ge (h .le (hp (by decide))))
  · exact hy ((h .disjoint (hp (by decide))).eq_bot_of_ge (h .ge (hp (by decide))))
  · exact hx' ((h .codisjoint (hp (by decide))).eq_top_of_le (h .ge (hp (by decide))))

/-- **Why seven**: of the sixteen conjunctions of atomic constraints,
exactly the seven in the range of `constraints` are nondegenerately
realizable — here already on the three-atom Boolean algebra; the other
nine force an argument to `⊥` or `⊤` on every bounded lattice
([maccartney-manning-2009]'s nontrivial-denotation proviso,
[icard-2012] §1). -/
theorem Relation.mem_range_constraints_iff {s : Finset Relation.Atom} :
    s ∈ Set.range Relation.constraints ↔
      ∃ x y : Finset (Fin 3), x ≠ ⊥ ∧ x ≠ ⊤ ∧ y ≠ ⊥ ∧ y ≠ ⊤ ∧
        ∀ a ∈ s, a.Holds x y := by
  constructor
  · rintro ⟨R, rfl⟩
    revert R; decide
  · rintro ⟨x, y, hx, hx', hy, hy', h⟩
    exact Relation.mem_range_constraints_of_holds h hx hx' hy hy'

/-! ### The join characterization and the strongest relation -/

/-- [icard-2012]'s Definition 1.4 as a characterization: `R.join S ≤ T`
exactly when chaining `R`'s content with `S`'s lands inside `T`'s —
soundness and tightness in one iff, the `sup_le_iff` idiom. -/
theorem Relation.join_le_iff {R S T : Relation} :
    R.join S ≤ T ↔
      ∀ x y z : Finset (Fin 3), R.Holds x y → S.Holds y z → T.Holds x z :=
  ⟨λ h _ _ _ hR hS => (hR.join hS).of_le h, λ h => (Relation.isLeast_join R S).2 h⟩

/-- [icard-2012]'s Lemma 1.3: any two elements distinct from `⊥` and `⊤`
stand in a strongest natural-logic relation — stated there for Boolean
lattices, proved here for any bounded lattice. It fails at `⊥`/`⊤`:
`x ⌣ ⊤` and `x ⊑ ⊤` hold with no common strengthening. -/
theorem Relation.exists_isLeast_holds {α : Type*} [Lattice α] [BoundedOrder α]
    {x y : α} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    ∃ R : Relation, IsLeast {S : Relation | S.Holds x y} R := by
  classical
  obtain ⟨R, hR⟩ := Relation.mem_range_constraints_of_holds
    (s := Finset.univ.filter (λ a => a.Holds x y))
    (λ a ha => (Finset.mem_filter.mp ha).2) hx hx' hy hy'
  refine ⟨R, Relation.holds_iff.mpr (λ a ha => ?_),
    λ S hS => Relation.le_iff.mpr (λ a ha => ?_)⟩
  · rw [hR] at ha
    exact (Finset.mem_filter.mp ha).2
  · rw [hR]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.holds_iff.mp hS a ha⟩


/-! ### Tightness of the projection tables -/

set_option synthInstance.maxSize 400 in
/-- **Tightness of the projection tables** ([icard-2012] Definition 2.3;
his Lemma 2.4 as an equality): `project R σ` is the least relation `T`
such that every σ-function sends `R`-pairs to `T`-pairs, already over
the two-element Boolean algebra. -/
theorem Signature.isLeast_project (R : Relation) (σ : Signature) :
    IsLeast {T : Relation | ∀ f : Finset (Fin 1) → Finset (Fin 1),
      σ.HoldsFor f → ∀ x y, R.Holds x y → T.Holds (f x) (f y)}
      (Signature.project R σ) := by
  refine ⟨λ f hf x y hR => σ.soundFor_of_holdsFor hf R x y hR, λ T hT => ?_⟩
  by_contra hle
  have counter : ∀ (R : Relation) (σ : Signature) (T : Relation),
      ¬ Signature.project R σ ≤ T →
      ∃ f : Finset (Fin 1) → Finset (Fin 1), σ.HoldsFor f ∧
        ∃ x y, R.Holds x y ∧ ¬ T.Holds (f x) (f y) := by decide
  obtain ⟨f, hf, x, y, hR, hT'⟩ := counter R σ T hle
  exact hT' (hT f hf x y hR)

/-- The refinement order on signatures is inclusion of function classes —
[icard-2012]'s semantic definition of ≼ (§2.2) recovered as a
characterization of the property-set order, with countermodels on the
two-element Boolean algebra. -/
theorem Signature.le_iff_holdsFor {σ τ : Signature} :
    σ ≤ τ ↔
      ∀ f : Finset (Fin 1) → Finset (Fin 1), σ.HoldsFor f → τ.HoldsFor f := by
  refine ⟨λ h f hf => hf.of_le h, λ h => ?_⟩
  by_contra hle
  have counter : ∀ σ τ : Signature, ¬ σ ≤ τ →
      ∃ f : Finset (Fin 1) → Finset (Fin 1), σ.HoldsFor f ∧ ¬ τ.HoldsFor f := by
    decide
  obtain ⟨f, hσ, hτ⟩ := counter σ τ hle
  exact hτ (h f hσ)

/-! ### Tightness of signature composition -/

set_option synthInstance.maxSize 400 in
theorem Signature.holdsFor_comp :
    ∀ (ψ φ : Signature) (f g : Finset (Fin 1) → Finset (Fin 1)),
      ψ.HoldsFor f → φ.HoldsFor g → (ψ * φ).HoldsFor (f ∘ g) := by decide

set_option synthInstance.maxSize 400 in
/-- **Tightness of signature composition** ([icard-2012]
Definition 2.6): `ψ * φ` is the least signature whose class contains
every composite of a ψ-function after a φ-function. -/
theorem Signature.isLeast_compose (ψ φ : Signature) :
    IsLeast {χ : Signature | ∀ f g : Finset (Fin 1) → Finset (Fin 1),
      ψ.HoldsFor f → φ.HoldsFor g → χ.HoldsFor (f ∘ g)} (ψ * φ) := by
  refine ⟨λ f g hf hg => Signature.holdsFor_comp ψ φ f g hf hg, λ χ hχ => ?_⟩
  by_contra hle
  have counter : ∀ ψ φ χ : Signature, ¬ ψ * φ ≤ χ →
      ∃ f g : Finset (Fin 1) → Finset (Fin 1),
        ψ.HoldsFor f ∧ φ.HoldsFor g ∧ ¬ χ.HoldsFor (f ∘ g) := by decide
  obtain ⟨f, g, hf, hg, hχ'⟩ := counter ψ φ χ hle
  exact hχ' (hχ f g hf hg)

end NaturalLogic
