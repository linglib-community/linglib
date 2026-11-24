/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Inflection.Linkage
public import Linglib.Morphology.ParadigmFunctionMorphology.Function

/-!
# The paradigm function as a paradigm linkage

Under the default rule of paradigm linkage, what a linkage realizes at a content cell is the value
of the paradigm function there. The structure `Linkage` is shared with accounts that have no
paradigm function, so this file is the one that relates the two.

## Main results

* `Morphology.Linkage.realized_eq_paradigmFunction`: under the default rule of paradigm linkage,
  the realization of a content cell is the paradigm function.

## References

* [stump-2006]
* [bonami-stump-2016]
-/

@[expose] public section

namespace Morphology.PFM

variable {L Z P : Type*} [PartialOrder P] [DecidableEq L] [DecidableLE P] [DecidableLT P]

/-- Under the default rule of paradigm linkage (27), with property-preserving property mapping,
form cells realized by the block cascade at their stem's L-index, and the convention (11) that a
basic stem's L-index is its lexeme, a content cell realizes as the paradigm function. -/
theorem _root_.Morphology.Linkage.realized_eq_paradigmFunction [DecidableEq Z]
    (ℓ : Linkage L Z P P) (lindex : Z → L) (stem : L × P → Z) (bs : List (Block L Z P))
    (h : ℓ.IsPropertyPreserving id) (hstem : ∀ l σ, ℓ.realize l σ = {stem (l, σ)})
    (hl : ∀ c, lindex (stem c) = c.1) (l : L) (σ : P) :
    ℓ.realized (fun z τ ↦ evalBlocks bs (lindex z, τ) z) l σ
      = {(paradigmFunction stem bs (l, σ), σ)} := by
  simp [Linkage.realized, h l σ, hstem, hl, paradigmFunction]

end Morphology.PFM
