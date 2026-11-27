/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Morphology.Word.Features
public import Linglib.Syntax.Feature.Bundle

/-!
# The agreement bundle of token features

Five of a token's features are dimensions of agreement: person, number, gender, case and
definiteness. The agreement bundle of a token's features keeps their values, the person slot
from the token's person and clusivity together, and forgets the other features. The map is
monotone: more specific features give a more specific bundle.

## Main definitions

* `Agreement.Bundle.ofFeatures`: the agreement bundle of a token's features.
* `Agreement.Bundle.ofFeaturesHom`: the same as an order homomorphism.

## References

* [corbett-2006]
* [de-marneffe-zeman-2021]
-/

@[expose] public section

namespace Agreement.Bundle

/-- The agreement bundle of a token's features keeps their values in the five dimensions. -/
def ofFeatures (f : Morphology.Features) : Bundle
  | .person => (f .person, f .clusivity)
  | .number => f .number
  | .gender => f .gender
  | .case => f .case
  | .definiteness => f .definiteness

@[simp] theorem ofFeatures_person (f : Morphology.Features) :
    ofFeatures f .person = (f .person, f .clusivity) :=
  rfl

@[simp] theorem ofFeatures_number (f : Morphology.Features) : ofFeatures f .number = f .number :=
  rfl

@[simp] theorem ofFeatures_gender (f : Morphology.Features) : ofFeatures f .gender = f .gender :=
  rfl

@[simp] theorem ofFeatures_case (f : Morphology.Features) : ofFeatures f .case = f .case := rfl

@[simp] theorem ofFeatures_definiteness (f : Morphology.Features) :
    ofFeatures f .definiteness = f .definiteness :=
  rfl

/-- More specific features give a more specific bundle. -/
theorem ofFeatures_mono : Monotone ofFeatures := fun _ _ h d ↦ by
  cases d
  · exact ⟨h .person, h .clusivity⟩
  all_goals exact h _

/-- `ofFeatures` as an order homomorphism. -/
@[simps]
def ofFeaturesHom : Morphology.Features →o Bundle := ⟨ofFeatures, ofFeatures_mono⟩

end Agreement.Bundle
