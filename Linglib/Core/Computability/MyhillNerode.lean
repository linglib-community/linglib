/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins

[UPSTREAM] candidate: `Mathlib.Computability.MyhillNerode`, beside
`Language.IsRegular.of_finite_range_leftQuotient`.
-/
module

public import Mathlib.Basic.Finite.Set
public import Mathlib.Computability.MyhillNerode
public import Linglib.Core.Logic.Function.FactorsThrough

/-!
# Regularity from a finite invariant

This file adds two consequences of the Myhill–Nerode theorem for languages. A language is regular
when membership is decided by an invariant of the word that takes finitely many values and is
preserved by appending on the right, and a regular language has only finitely many pairwise
distinguishable words.

## Main results

* `Language.IsRegular.of_factorsThrough`: a language whose membership factors through a map with
  finite range, compatible with appending on the right, is regular.
* `Language.IsRegular.finite_of_injective_leftQuotient`: a family of words with pairwise distinct
  left quotients by a regular language is finite.

## References

* [hopcroft-ullman-1979]
-/

@[expose] public section

namespace Language

variable {α β : Type*} {L : Language α}

theorem IsRegular.of_factorsThrough {g : List α → β} (hL : Function.FactorsThrough (· ∈ L) g)
    (hg : ∀ ⦃u v⦄ (x : List α), g u = g v → g (u ++ x) = g (v ++ x))
    (hfin : (Set.range g).Finite) : L.IsRegular :=
  .of_finite_range_leftQuotient <| Function.FactorsThrough.finite_range
    (fun _ _ e ↦ Set.ext fun x ↦ iff_of_eq (hL (hg x e))) hfin

theorem IsRegular.finite_of_injective_leftQuotient (h : L.IsRegular) {ι : Type*}
    {f : ι → List α} (hf : (L.leftQuotient ∘ f).Injective) : Finite ι :=
  have := (h.finite_range_leftQuotient.subset (Set.range_comp_subset_range f _)).to_subtype
  Finite.of_injective_finite_range hf

end Language
