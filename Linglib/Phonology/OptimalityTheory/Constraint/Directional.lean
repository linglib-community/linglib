/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.OptimalityTheory.Constraint.Defs

/-!
# Directional constraints as position-indexed blocks

A directional constraint ([eisner-2000], [lamont-2022b]) maps each candidate to a vector of
violations by position, compared lexicographically. As [lamont-2022b] (§1.3) observes, "a locus at
position `i` relates to one at `i+1` exactly as a higher-ranked constraint relates to a lower one …
violation vectors are ordered lexicographically, which is exactly how candidates are ordered with
respect to an entire constraint set in OT". A directional constraint with single-segment loci over
a length-preserving GEN is therefore a block of binary constraints, one per position, spliced into
a ranking and compared under the lexicographic order of `ViolationProfile`
(`List.ofFn_le_ofFn_iff`).

`directionalBlock n locus` is that block. Spliced forward it evaluates left to right, and reversed
it evaluates right to left, since "the positions are reversed in the violation vector"
([lamont-2022b] §1.3, Fig 1.9). The constraint against floating tones of [mcpherson-lamont-2026]
and `Parse(σ)` of [lamont-2022c] are such blocks.

## Implementation notes

Only single-segment loci and length-preserving GEN are covered, which is the case of a floating
tone and of an unfooted syllable. [lamont-2022b]'s general formulation also handles multi-segment
loci (the opposite-edge projection that rules out "locus folding", §2.3) and length-changing GEN
(step-relative positions, fn. 10).

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

/-- A **directional constraint** with single-segment loci over length-preserving GEN
([lamont-2022b]): the position-indexed block of binary constraints `i ↦ ⟦locus i⟧`,
for positions `i < n`. Spliced into a ranking and compared under the canonical lex
profile this is directional EVAL — `⇒` (left-to-right) for the forward block, `⇐` for
`.reverse`. The block's `i`-th coordinate is exactly the directional violation vector's
`i`-th entry, so the spliced profile equals the directional one
(`List.ofFn_le_ofFn_iff`). -/
def directionalBlock {C : Type*} (n : ℕ) (locus : Fin n → C → Prop)
    [∀ i, DecidablePred (locus i)] : List (Constraint C) :=
  (List.finRange n).map fun i ↦ binary (locus i)

end OptimalityTheory.Constraint
