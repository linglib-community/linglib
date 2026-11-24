/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.DistributedMorphology.Realization
public import Linglib.Morphology.Exponence.SubsetRule

/-!
# Vocabulary Items as subset rules

A Vocabulary Item is a rule of the Subset Principle whose features are positioned: its site is a
finite set of pairs of an offset and a feature, and it applies in a neighborhood exactly when its
site is contained in the neighborhood's positioned features. The Subset Principle is then
selection among the items as subset rules, and Vocabulary Insertion is their realization.

## Main definitions

* `DistributedMorphology.VocabularyItem.subsetRuleEquiv`: a Vocabulary Item as a subset rule over
  sets of positioned features.

## Main results

* `DistributedMorphology.VocabularyItem.applies_subsetRuleEquiv_iff`: an item applies in a
  neighborhood exactly when, as a subset rule, it applies to the neighborhood's positioned
  features.
* `DistributedMorphology.subsetPrinciple_eq_realize_map`: the Subset Principle is selection among
  the items as subset rules.
* `DistributedMorphology.toRealization_eq_map`: Vocabulary Insertion is the realization of the
  items as subset rules.

## References

* [halle-marantz-1993]
* [halle-1997]
-/

@[expose] public section

namespace DistributedMorphology.VocabularyItem

open Morphology

variable {F E : Type*} {i : VocabularyItem F E} {n : Neighborhood (Finset F)}

/-- A Vocabulary Item is a rule of the Subset Principle whose features are positioned. -/
def subsetRuleEquiv : VocabularyItem F E ≃ SubsetRule (Finset (ℤ × F)) E where
  toFun i := ⟨i.site, i.exponent⟩
  invFun r := ⟨r.features, r.exponent⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem features_subsetRuleEquiv (i : VocabularyItem F E) :
    (subsetRuleEquiv i).features = i.site := rfl

@[simp] theorem exponent_subsetRuleEquiv (i : VocabularyItem F E) :
    (subsetRuleEquiv i).exponent = i.exponent := rfl

/-- An item applies in a neighborhood exactly when, as a subset rule, it applies to the
neighborhood's positioned features. -/
theorem applies_subsetRuleEquiv_iff [DecidableEq F] :
    Applies (subsetRuleEquiv i) n.toFinset ↔ Applies i n := by
  rw [applies_iff_subset_toFinset]
  rfl

end DistributedMorphology.VocabularyItem

namespace DistributedMorphology

open Morphology VocabularyItem

variable {F E : Type*} [DecidableEq F]

/-- The Subset Principle is selection among the items as subset rules, at the positioned features
of the neighborhood. -/
theorem subsetPrinciple_eq_realize_map (items : RuleSet (VocabularyItem F E))
    (n : Neighborhood (Finset F)) :
    subsetPrinciple items n =
      RuleSet.realize (items.map subsetRuleEquiv) (specificity ∘ subsetRuleEquiv.symm)
        n.toFinset := by
  rw [subsetPrinciple, RuleSet.realize, RuleSet.realize,
    RuleSet.selectBy_map (c := n) (f := specificity)
      (fun _ _ ↦ applies_subsetRuleEquiv_iff) (fun _ _ _ _ ↦ Iff.rfl), Option.map_map]
  rfl

/-- Vocabulary Insertion is the realization of the items as subset rules. -/
theorem toRealization_eq_map {R Ctx : Type*} (items : RuleSet (VocabularyItem F E))
    (site : R → Ctx → Neighborhood (Finset F)) :
    toRealization items site =
      RuleSet.toRealization (items.map subsetRuleEquiv) (specificity ∘ subsetRuleEquiv.symm)
        fun r c ↦ (site r c).toFinset := by
  ext r c : 3
  simp only [toRealization_realize, RuleSet.toRealization_realize, subsetPrinciple_eq_realize_map]

end DistributedMorphology
