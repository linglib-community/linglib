/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Diagram
public import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Transderivational correspondence

This file defines Benua's transderivational correspondence theory, in which a derived word and its
base stand in an output–output correspondence whose identity constraints are ranked with
markedness and with the faithfulness of each word to its own input. A candidate is a subparadigm,
the two words with their inputs and the three relations. Every constraint of the hierarchy is read
at both words, and recursive evaluation ranks the copy that evaluates the base above the copy that
evaluates the derived word.

## Main definitions

* `Transderivational.paradigm`, `Transderivational.paradigmOfPairs`: a subparadigm, its OO
  relation induced by the two IO relations or given.
* `Transderivational.ParadigmConstraint`: a constraint read at the base and at the derived word,
  with `markedness`, `ioFaith` and `ooIdentity`.
* `Transderivational.recursive`, `Transderivational.nonrecursive`: the hierarchy's copies for the
  base and the derived word in rank order, and the tally of each constraint over both words.

## Main statements

* `Transderivational.optimal_ofLabels_recursive`: under recursive evaluation the winners are the
  derived word's winners among the subparadigms whose base wins.
* `Transderivational.eq_zero_of_mem_optimal_ofLabels_nonrecursive`: under summed evaluation, a
  candidate satisfying the top constraints in both words forces every winner to.

## Implementation notes

* OO-Identity is vacuous at the base, a simplex word that bears no OO relation of its own.
* An OO-Identity constraint is proper to one OO relation, and is vacuous on subparadigms bearing
  another, so that affixes subcategorizing for different relations share one hierarchy.

## References

* [benua-1997]
-/

@[expose] public section

namespace OptimalityTheory.Transderivational

variable {α ρ L : Type*}

/-- The four positions of a subparadigm, each word with its own input. -/
inductive Role
  | baseInput | base | derivInput | derivative
  deriving DecidableEq, Repr

/-- The subparadigm of a base `b` and a derived word `d` with their inputs, the index pairs of
their IO relations, and the index pairs `oo` of their OO relation. -/
def paradigmOfPairs (bIn b dIn d : List α) (ioB ioD oo : List (ℕ × ℕ)) :
    Correspondence.Diagram Role α :=
  .ofPairs (fun | .baseInput => bIn | .base => b | .derivInput => dIn | .derivative => d)
    fun | .baseInput, .base => ioB | .derivInput, .derivative => ioD | .base, .derivative => oo
        | _, _ => []

/-- The subparadigm whose OO relation the IO relations induce (`Correspondence.ooPairs`): the base's
input stands in the derived word's at `offset`, so that the OO relation links the realisations of
each segment of the base's input, and the epenthetic segments at a common site. -/
def paradigm (bIn b dIn d : List α) (ioB ioD : List (ℕ × ℕ)) (offset : ℕ := 0) :
    Correspondence.Diagram Role α :=
  paradigmOfPairs bIn b dIn d ioB ioD
    (Correspondence.ooPairs (ioB.map fun rp ↦ (rp.1 + offset, rp.2)) ioD b.length d.length)

/-- A constraint of the hierarchy, read at each word of the subparadigm. -/
structure ParadigmConstraint (α : Type*) where
  /-- The violations the base incurs. -/
  atBase : Correspondence.Diagram Role α → ℕ
  /-- The violations the derived word incurs. -/
  atDerived : Correspondence.Diagram Role α → ℕ

/-- A markedness constraint, read off each output. -/
def markedness (m : List α → ℕ) : ρ → ParadigmConstraint α :=
  fun _ ↦ ⟨fun c ↦ m (c.form .base), fun c ↦ m (c.form .derivative)⟩

/-- An IO-Faith constraint, read off each word's IO relation. -/
def ioFaith (f : Correspondence.Diagram Role α → Role → Role → ℕ) : ρ → ParadigmConstraint α :=
  fun _ ↦ ⟨fun c ↦ f c .baseInput .base, fun c ↦ f c .derivInput .derivative⟩

/-- The OO-Identity constraint proper to the relation `rel` is read off the OO relation of a
subparadigm bearing `rel`, and is vacuous on subparadigms bearing another and at the base. -/
def ooIdentity [DecidableEq ρ] (rel : ρ) (f : Correspondence.Diagram Role α → Role → Role → ℕ) :
    ρ → ParadigmConstraint α :=
  fun r ↦ ⟨fun _ ↦ 0, fun c ↦ if r = rel then f c .base .derivative else 0⟩

/-- The copy of the hierarchy that evaluates the base of a subparadigm bearing `r`. -/
def baseRecursion (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence.Diagram Role α)) :=
  ranking.map fun k ↦ (k r).atBase

/-- The copy of the hierarchy that evaluates the derived word of a subparadigm bearing `r`. -/
def derivedRecursion (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence.Diagram Role α)) :=
  ranking.map fun k ↦ (k r).atDerived

/-- Recursive evaluation duplicates the hierarchy and ranks the base's copy above the derived
word's. -/
def recursive (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence.Diagram Role α)) :=
  baseRecursion ranking r ++ derivedRecursion ranking r

/-- Summed evaluation tallies each constraint's violations over both words. -/
def nonrecursive (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence.Diagram Role α)) :=
  ranking.map fun k c ↦ (k r).atBase c + (k r).atDerived c

variable {cand : L → Correspondence.Diagram Role α} {labels : Finset L}
  {ranking : List (ρ → ParadigmConstraint α)} {r : ρ}

/-- Base priority is ranking priority: the winners of recursive evaluation are the derived word's
winners among the subparadigms whose base wins its own copy of the hierarchy. -/
theorem optimal_ofLabels_recursive :
    (Tableau.ofLabels cand labels (recursive ranking r)).optimal =
      (Tableau.ofLabels cand (Tableau.ofLabels cand labels (baseRecursion ranking r)).optimal
        (derivedRecursion ranking r)).optimal :=
  Tableau.optimal_ofLabels_append

/-- When the candidates share their base, recursive evaluation is evaluation of the derived
word. -/
theorem optimal_ofLabels_recursive_of_forall_eq
    (h : ∀ k ∈ ranking, ∀ x ∈ labels, ∀ y ∈ labels, (k r).atBase (cand x) = (k r).atBase (cand y)) :
    (Tableau.ofLabels cand labels (recursive ranking r)).optimal =
      (Tableau.ofList labels (ranking.map fun k ↦ (k r).atDerived ∘ cand)).optimal := by
  rw [Tableau.ofLabels, recursive, List.map_append, Tableau.optimal_ofList_append_of_forall_eq]
  · rw [derivedRecursion, List.map_map]
    rfl
  · simp only [baseRecursion, List.map_map, List.mem_map, Function.comp_apply]
    rintro _ ⟨k, hk, rfl⟩ x hx y hy
    exact h k hk x hx y hy

/-- Without recursion underapplication is never optimal: under summed evaluation, if some
subparadigm satisfies the top constraints in both words, as overapplication satisfies OO-Identity
and the markedness constraint driving the process, so does every winner. -/
theorem eq_zero_of_mem_optimal_ofLabels_nonrecursive {top rest : List (ρ → ParadigmConstraint α)}
    {x y : L} (hy : y ∈ (Tableau.ofLabels cand labels (nonrecursive (top ++ rest) r)).optimal)
    (hx : x ∈ labels) (h0 : ∀ k ∈ top, (k r).atBase (cand x) = 0 ∧ (k r).atDerived (cand x) = 0) :
    ∀ k ∈ top, (k r).atBase (cand y) = 0 ∧ (k r).atDerived (cand y) = 0 := by
  rw [Tableau.ofLabels, nonrecursive, List.map_append, List.map_append] at hy
  have := Tableau.eq_zero_of_mem_optimal_ofList_append hy hx (by
    simp only [List.map_map, List.mem_map, Function.comp_apply]
    rintro _ ⟨k, hk, rfl⟩
    simp [Constraint.comap, h0 k hk])
  intro k hk
  simpa [Constraint.comap] using this _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨k, hk, rfl⟩, rfl⟩)

end OptimalityTheory.Transderivational
