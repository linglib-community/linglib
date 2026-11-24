/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Realization.Map

/-!
# Inflection classes

An inflection class is a class of lexemes that inflect in the same way, showing the same
allomorphy in all the word-forms of their paradigm. Taken as a realization `S` of lexemes by
exponents in each cell, two lexemes inflect in the same way when `S.realize` gives them the same
exponents in every cell, so the inflection classes are the classes of `Setoid.ker S.realize`, and
the realization of the classes is the reduction `S.reduce`, of which `S` is the pullback.

A classification `cls` of the lexemes, such as the declensions of a grammar, determines their
inflection when lexemes of one class inflect in the same way, `Setoid.ker cls ≤ Setoid.ker
S.realize`. This holds exactly when `S` is a pullback along `cls`, a realization of the classes
read at the class of each lexeme. The inflection classes are the coarsest such classification.

## Main results

* `Realization.exists_eq_comap_id_iff`: a classification of the indices determines their forms
  exactly when the realization is a pullback along it.

## TODO

* A `ParadigmSystem` whose rows are inflection classes is the reduction of the realization of a
  language's lexemes; state `ParadigmSystem.ParadigmEconomy` and the principal parts of
  `Morphology/Inflection/Paradigm/Complexity.lean` of a reduction.
* The declension classes of the language files, such as `Czech.Declension.Class`, determine the
  endings of their nouns; state it with `Realization.exists_eq_comap_id_iff`.
* Heteroclisis, a lexeme whose cells follow two classes, is `Linkage.IsHeteroclite`, stated of
  stems; relate it to a classification that determines inflection in each cell separately.

## References

* [haspelmath-sims-2010]
* [stump-2016]
-/

@[expose] public section

namespace Morphology.Realization

variable {R Ctx F K : Type*}

/-- A classification of the indices determines their forms exactly when the realization is a
pullback along it. -/
theorem exists_eq_comap_id_iff (S : Realization R Ctx F) (cls : R → K) :
    (∃ T : Realization K Ctx F, S = T.comap cls id) ↔
      Setoid.ker cls ≤ Setoid.ker S.realize := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ker_le_ker_comap_realize cls id T
  · intro h
    have hf : Function.FactorsThrough S.realize cls := fun _ _ hab ↦ h hab
    refine ⟨⟨Function.extend cls S.realize fun _ _ ↦ ∅⟩, ?_⟩
    ext r c : 3
    exact congrFun (hf.extend_apply (fun _ _ ↦ ∅) r).symm c

end Morphology.Realization
