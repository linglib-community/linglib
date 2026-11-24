/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Realization.Map

/-!
# Conditioning of allomorphs

A morpheme with more than one shape has allomorphs, which have the same meaning and occur in
complementary distribution. The conditioning of the allomorphy is what determines the choice among
them: the phonological context, the morphological context, or the individual lexical item. Taken
as a realization `S` of morphemes by shapes, an allomorphy is conditioned by a map `k` of its
contexts when the shapes of each morpheme depend on the context only through `k`, that is
`Function.FactorsThrough (S.realize r) k` for each `r`. A realization is conditioned by `k`
exactly when it is a pullback along `k`.

## Main results

* `Realization.factorsThrough_realize_comap`: the forms of an index in a pullback along `k` depend
  on the context only through `k`.
* `Realization.exists_eq_comap_iff`: a realization is a pullback along `k` exactly when the forms
  of each index depend on the context only through `k`.

## TODO

* Phonological, morphological and lexical conditioning as three choices of `k`: the shape of the
  neighbouring form, the cell, and the lexical item.
* Welded forms: a bound form is welded when it has shape variants phonologically conditioned by
  its host, or phonologically conditions shape variants of its host ([haspelmath-2021c]).
  `Studies/Haspelmath2021c` identifies Italian *mi* with *-mmi* and English *a* with *an* by hand.
* `Realization.IsSuppletive` holds of an index with two or more forms, which [haspelmath-
  sims-2010] call allomorphy; their suppletion is the allomorphy that no phonological rule
  describes. Say which is meant where the two differ.

## References

* [haspelmath-sims-2010]
* [haspelmath-2021c]
-/

@[expose] public section

namespace Morphology.Realization

variable {R Ctx F K : Type*}

/-- The forms of an index in a pullback along `k` depend on the context only through `k`. -/
theorem factorsThrough_realize_comap {R₁ : Type*} (i : R₁ → R) (k : Ctx → K)
    (T : Realization R K F) (r : R₁) : Function.FactorsThrough ((T.comap i k).realize r) k :=
  fun _ _ h ↦ by simp only [comap_realize, h]

/-- A realization is a pullback along a map `k` of contexts exactly when the forms of each index
depend on the context only through `k`. -/
theorem exists_eq_comap_iff (S : Realization R Ctx F) (k : Ctx → K) :
    (∃ T : Realization R K F, S = T.comap id k) ↔
      ∀ r, Function.FactorsThrough (S.realize r) k := by
  constructor
  · rintro ⟨T, rfl⟩ r
    exact factorsThrough_realize_comap id k T r
  · intro h
    refine ⟨⟨fun r ↦ Function.extend k (S.realize r) fun _ ↦ ∅⟩, ?_⟩
    ext r c : 3
    rw [comap_realize]
    exact ((h r).extend_apply (fun _ ↦ ∅) c).symm

end Morphology.Realization
