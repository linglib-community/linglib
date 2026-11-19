/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs

/-!
# Directional constraints

A directional constraint assigns each candidate a vector of violations indexed by position, and
candidates are compared by the lexicographic order on these vectors, as in Eisner's directional
evaluation and Lamont's Directional Harmonic Serialism. Lamont observes that a locus at one
position relates to a locus at the next exactly as a higher-ranked constraint relates to a lower
one. A directional constraint with single-segment loci over a length-preserving GEN is therefore a
block of binary constraints, one per position, spliced into the ranking and compared under the
lexicographic order of violation profiles. Spliced forward the block evaluates from left to right,
and reversed it evaluates from right to left. The constraint against floating tones of McPherson
and Lamont and `Parse(σ)` in Lamont's theory of footing are such blocks.

## Implementation notes

Only single-segment loci and length-preserving GEN are covered, which are the cases of a floating
tone and of an unfooted syllable. Lamont's general formulation also admits loci spanning several
segments and a GEN that changes the length of the form.

## References

* [J. Eisner, *Directional Constraint Evaluation in Optimality Theory* (2000)][eisner-2000]
* [A. Lamont, *Directional Harmonic Serialism* (2022)][lamont-2022b]
* [A. Lamont, *A Restrictive, Parsimonious Theory of Footing in Directional Harmonic Serialism*
  (2022)][lamont-2022c]
* [L. McPherson and A. Lamont, *Poko postlexical tone requires serial, directional evaluation*
  (2026)][mcpherson-lamont-2026]
-/

@[expose] public section

namespace OptimalityTheory.Constraint

/-- The block of binary constraints that flags `locus i` at each position `i < n`, a directional
constraint with single-segment loci ([lamont-2022b], pp. 16–17). -/
def directionalBlock {C : Type*} (n : ℕ) (locus : Fin n → C → Prop)
    [∀ i, DecidablePred (locus i)] : List (Constraint C) :=
  (List.finRange n).map fun i ↦ binary (locus i)

end OptimalityTheory.Constraint
