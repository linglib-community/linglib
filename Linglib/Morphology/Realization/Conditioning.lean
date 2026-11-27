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
as a realization `S` of morphemes by shapes, the shapes of a morpheme `r` are conditioned by a
map `k` of the contexts when, among the contexts that license `r`, they depend on the context
only through `k`. Every morpheme is conditioned by `k` exactly when the realization agrees with a
pullback along `k` wherever it licenses a morpheme, and a realization that licenses every
morpheme in every context is then the pullback itself.

## Main definitions

* `Realization.IsConditionedBy`: the forms of an index depend on the contexts that license it only
  through a map of contexts.

## Main results

* `Realization.forall_isConditionedBy_iff`: every index is conditioned by `k` exactly when the
  realization agrees with a pullback along `k` wherever it licenses an index.
* `Realization.isConditionedBy_iff_factorsThrough`: an index licensed in every context is
  conditioned by `k` exactly when its forms depend on the context only through `k`.
* `Realization.exists_eq_comap_iff`: a realization is a pullback along `k` exactly when the forms
  of each index depend on the context only through `k`.
* `Realization.isConditionedBy_const_iff`: an index is conditioned by a constant map exactly when
  it is not properly suppletive.

## Implementation notes

Conditioning is asked only of the contexts that license an index. A realization read off a set of
observed forms is empty at the contexts that were not observed, and asking the forms to agree
there too would make the shapes of the English article fail to depend on the following sound,
since the article is not observed before every word that begins with a vowel.

## TODO

* Phonological, morphological and lexical conditioning are three choices of `k`, the shape of
  the neighbouring form, the cell and the lexical item, and need no definitions of their own. A
  study of an allomorphy states which `k` conditions it.
* Welded forms: a bound form is welded when it has shape variants phonologically conditioned by
  its host, or phonologically conditions shape variants of its host ([haspelmath-2021c]). The
  first clause is `IsConditionedBy` of a form's shapes by the class of its neighbour. The second
  needs the host's default shape, which a realization does not single out and a rule set does.
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

variable {R Ctx F K K' : Type*}

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

/-! ### Conditioning where an index is licensed -/

variable (S : Realization R Ctx F)

/-- The forms of `r` are conditioned by a map `k` of contexts when, among the contexts that
license `r`, they depend on the context only through `k`. -/
def IsConditionedBy (k : Ctx → K) (r : R) : Prop :=
  ∀ ⦃c c'⦄, S.IsLicensed r c → S.IsLicensed r c' → k c = k c' → S.realize r c = S.realize r c'

variable {S} {k : Ctx → K} {r : R}

theorem isConditionedBy_id : S.IsConditionedBy id r := fun _ _ _ _ h ↦ congrArg _ h

/-- Forms that depend on every context only through `k` are conditioned by `k`. -/
theorem IsConditionedBy.of_factorsThrough (h : Function.FactorsThrough (S.realize r) k) :
    S.IsConditionedBy k r := fun _ _ _ _ hk ↦ h hk

/-- An index licensed in every context is conditioned by `k` exactly when its forms depend on the
context only through `k`. -/
theorem isConditionedBy_iff_factorsThrough (h : ∀ c, S.IsLicensed r c) :
    S.IsConditionedBy k r ↔ Function.FactorsThrough (S.realize r) k :=
  ⟨fun hk c c' hc ↦ hk (h c) (h c') hc, .of_factorsThrough⟩

/-- Forms conditioned by a coarser map of contexts are conditioned by a finer one. -/
theorem IsConditionedBy.of_comp {g : K → K'} (h : S.IsConditionedBy (g ∘ k) r) :
    S.IsConditionedBy k r := fun _ _ hc hc' hk ↦ h hc hc' (congrArg g hk)

/-- The forms of an index are conditioned by a constant map exactly when the index is not
properly suppletive. -/
theorem isConditionedBy_const_iff (κ : K) :
    S.IsConditionedBy (fun _ ↦ κ) r ↔ ¬ S.IsProperlySuppletive r := by
  simp only [IsConditionedBy, IsProperlySuppletive, forall_const, not_exists, not_and, not_not]

/-- Where a realization has at most one form in a cell, a form conditioned by `k` is a function
of the class of the context. -/
theorem IsConditionedBy.eq_of_mem (h : S.IsConditionedBy k r) (hS : S.IsUnivalent)
    {c c' : Ctx} {f f' : F} (hf : f ∈ S.realize r c) (hf' : f' ∈ S.realize r c')
    (hk : k c = k c') : f = f' :=
  hS r hf (show f' ∈ S.realize r c from h ⟨f, hf⟩ ⟨f', hf'⟩ hk ▸ hf')

/-- Every index of a realization is conditioned by `k` exactly when the realization agrees with a
pullback along `k` wherever it licenses an index. -/
theorem forall_isConditionedBy_iff (S : Realization R Ctx F) (k : Ctx → K) :
    (∀ r, S.IsConditionedBy k r) ↔
      ∃ T : Realization R K F, ∀ r c, S.IsLicensed r c → S.realize r c = T.realize r (k c) := by
  constructor
  · intro h
    have hf (r : R) : Function.FactorsThrough (fun c : {c // S.IsLicensed r c} ↦ S.realize r c)
        fun c ↦ k c := fun a b hab ↦ h r a.2 b.2 hab
    exact ⟨⟨fun r ↦ Function.extend (fun c : {c // S.IsLicensed r c} ↦ k c)
      (fun c ↦ S.realize r c) fun _ ↦ ∅⟩,
      fun r c hc ↦ ((hf r).extend_apply (fun _ ↦ ∅) ⟨c, hc⟩).symm⟩
  · rintro ⟨T, hT⟩ r c c' hc hc' hk
    rw [hT r c hc, hT r c' hc', hk]

instance [Fintype Ctx] [DecidableEq K] [DecidableEq F] (S : Realization R Ctx F) (k : Ctx → K)
    (r : R) : Decidable (S.IsConditionedBy k r) :=
  decidable_of_iff (∀ c c', S.IsLicensed r c → S.IsLicensed r c' → k c = k c' →
    S.realize r c = S.realize r c') ⟨fun h _ _ ↦ h _ _, fun h c c' ↦ @h c c'⟩

end Morphology.Realization
