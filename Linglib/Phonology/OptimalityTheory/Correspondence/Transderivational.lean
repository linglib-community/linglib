/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Correspondence.Coindexation
public import Linglib.Phonology.OptimalityTheory.Filtration

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

* `Transderivational.evalOn_recursive`: under recursive evaluation the winners are the
  derived word's winners among the subparadigms whose base wins.
* `Transderivational.eq_zero_of_mem_evalOn_nonrecursive`: under summed evaluation, a
  candidate satisfying the top constraints in both words forces every winner to.
* `Transderivational.evalOn_baseRecursion_ooIdentity`: an OO-Identity constraint never chooses
  among the candidates for a simplex word.

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
    Correspondence.Coindexation Role α :=
  .ofPairs (fun | .baseInput => bIn | .base => b | .derivInput => dIn | .derivative => d)
    [(.baseInput, .base, ioB), (.derivInput, .derivative, ioD), (.base, .derivative, oo)]

/-- The indices a position `j` of an output bears on the OO relation, given the index pairs
`io` of the output with an input of length `n`: the input positions it realises, or, when it
realises none, an index for its site, the last input position realised at or before it. -/
def ooIndices (n : ℕ) (io : List (ℕ × ℕ)) (j : ℕ) : List ℕ :=
  match ((io.filter fun p ↦ p.1 < n ∧ p.2 = j).map (·.1)) with
  | [] => [n + 1 + (((io.filter fun p ↦ p.1 < n ∧ p.2 ≤ j).map (·.1)).max?.getD n)]
  | l => l

/-- The subparadigm whose OO relation runs through the derived word's input: the base's input
stands in the derived word's at `offset`, so that the OO relation links the realisations of
each segment of the base's input, and the epenthetic segments at a common site. -/
def paradigm (bIn b dIn d : List α) (ioB ioD : List (ℕ × ℕ)) (offset : ℕ := 0) :
    Correspondence.Coindexation Role α where
  form
    | .baseInput => bIn.zipIdx.map fun x ↦ (x.1, fun | .base => [x.2] | _ => [])
    | .base => b.zipIdx.map fun x ↦ (x.1, fun
      | .baseInput => (ioB.filter (·.2 = x.2)).map (·.1)
      | .derivative => ooIndices dIn.length (ioB.map fun rp ↦ (rp.1 + offset, rp.2)) x.2
      | _ => [])
    | .derivInput => dIn.zipIdx.map fun x ↦ (x.1, fun | .derivative => [x.2] | _ => [])
    | .derivative => d.zipIdx.map fun x ↦ (x.1, fun
      | .derivInput => (ioD.filter (·.2 = x.2)).map (·.1)
      | .base => ooIndices dIn.length ioD x.2
      | _ => [])

/-- A constraint of the hierarchy, read at each word of the subparadigm. -/
structure ParadigmConstraint (α : Type*) where
  /-- The violations the base incurs. -/
  atBase : Correspondence.Coindexation Role α → ℕ
  /-- The violations the derived word incurs. -/
  atDerived : Correspondence.Coindexation Role α → ℕ

/-- A markedness constraint, read off each output. -/
def markedness (m : List α → ℕ) : ρ → ParadigmConstraint α :=
  fun _ ↦ ⟨fun c ↦ m (c.string .base), fun c ↦ m (c.string .derivative)⟩

/-- An IO-Faith constraint, read off each word's IO relation. -/
def ioFaith (f : Correspondence.Coindexation Role α → Role → Role → ℕ) : ρ → ParadigmConstraint α :=
  fun _ ↦ ⟨fun c ↦ f c .baseInput .base, fun c ↦ f c .derivInput .derivative⟩

/-- The OO-Identity constraint proper to the relation `rel` is read off the OO relation of a
subparadigm bearing `rel`, and is vacuous on subparadigms bearing another and at the base. -/
def ooIdentity [DecidableEq ρ] (rel : ρ)
    (f : Correspondence.Coindexation Role α → Role → Role → ℕ) :
    ρ → ParadigmConstraint α :=
  fun r ↦ ⟨fun _ ↦ 0, fun c ↦ if r = rel then f c .base .derivative else 0⟩

/-- The copy of the hierarchy that evaluates the base of a subparadigm bearing `r`. -/
def baseRecursion (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence.Coindexation Role α)) :=
  ranking.map fun k ↦ (k r).atBase

/-- The copy of the hierarchy that evaluates the derived word of a subparadigm bearing `r`. -/
def derivedRecursion (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence.Coindexation Role α)) :=
  ranking.map fun k ↦ (k r).atDerived

/-- Recursive evaluation duplicates the hierarchy and ranks the base's copy above the derived
word's. -/
def recursive (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence.Coindexation Role α)) :=
  baseRecursion ranking r ++ derivedRecursion ranking r

/-- Summed evaluation tallies each constraint's violations over both words. -/
def nonrecursive (ranking : List (ρ → ParadigmConstraint α)) (r : ρ) :
    List (Constraint (Correspondence.Coindexation Role α)) :=
  ranking.map fun k c ↦ (k r).atBase c + (k r).atDerived c

variable {cand : L → Correspondence.Coindexation Role α} {labels : Finset L}
  {ranking : List (ρ → ParadigmConstraint α)} {r : ρ}

/-- Base priority is ranking priority: the winners of recursive evaluation are the derived word's
winners among the subparadigms whose base wins its own copy of the hierarchy. -/
theorem evalOn_recursive :
    Constraint.evalOn cand labels (recursive ranking r) =
      Constraint.evalOn cand (Constraint.evalOn cand labels (baseRecursion ranking r))
        (derivedRecursion ranking r) :=
  Constraint.evalOn_append

/-- A simplex word bears no OO relation, so an OO-Identity constraint never chooses among the
candidates for a base: the base's copy of a hierarchy selects what it selects without the
constraint. -/
theorem evalOn_baseRecursion_ooIdentity [DecidableEq ρ] {top rest : List (ρ → ParadigmConstraint α)}
    (rel : ρ) (f : Correspondence.Coindexation Role α → Role → Role → ℕ) :
    Constraint.evalOn cand labels (baseRecursion (top ++ ooIdentity rel f :: rest) r) =
      Constraint.evalOn cand labels (baseRecursion (top ++ rest) r) := by
  simp only [Constraint.evalOn, baseRecursion, List.map_append, List.map_cons,
    Constraint.eval_append]
  exact Constraint.eval_cons_of_forall_eq fun _ _ _ _ ↦ rfl

/-- When the candidates share their base, recursive evaluation is evaluation of the derived
word. -/
theorem evalOn_recursive_of_forall_eq
    (h : ∀ k ∈ ranking, ∀ x ∈ labels, ∀ y ∈ labels, (k r).atBase (cand x) = (k r).atBase (cand y)) :
    Constraint.evalOn cand labels (recursive ranking r) =
      Constraint.eval labels (ranking.map fun k ↦ (k r).atDerived ∘ cand) := by
  rw [Constraint.evalOn, recursive, List.map_append, Constraint.eval_append_of_forall_eq]
  · rw [derivedRecursion, List.map_map]
    rfl
  · simp only [baseRecursion, List.map_map, List.mem_map, Function.comp_apply]
    rintro _ ⟨k, hk, rfl⟩ x hx y hy
    exact h k hk x hx y hy

/-- Without recursion underapplication is never optimal: under summed evaluation, if some
subparadigm satisfies the top constraints in both words, as overapplication satisfies OO-Identity
and the markedness constraint driving the process, so does every winner. -/
theorem eq_zero_of_mem_evalOn_nonrecursive {top rest : List (ρ → ParadigmConstraint α)} {x y : L}
    (hy : y ∈ Constraint.evalOn cand labels (nonrecursive (top ++ rest) r))
    (hx : x ∈ labels) (h0 : ∀ k ∈ top, (k r).atBase (cand x) = 0 ∧ (k r).atDerived (cand x) = 0) :
    ∀ k ∈ top, (k r).atBase (cand y) = 0 ∧ (k r).atDerived (cand y) = 0 := by
  rw [Constraint.evalOn, nonrecursive, List.map_append, List.map_append] at hy
  have := Constraint.eq_zero_of_mem_eval_append hy hx (by
    simp only [List.map_map, List.mem_map, Function.comp_apply]
    rintro _ ⟨k, hk, rfl⟩
    simp [Constraint.comap, h0 k hk])
  intro k hk
  simpa [Constraint.comap] using this _ (List.mem_map.2 ⟨_, List.mem_map.2 ⟨k, hk, rfl⟩, rfl⟩)

end OptimalityTheory.Transderivational
