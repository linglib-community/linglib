module

public import Linglib.Semantics.Conditionals.Counterfactual

/-!
# McKay and van Inwagen (1977): Counterfactuals with Disjunctive Antecedents

This file formalizes the defence in [mckay-vaninwagen-1977] of the variably strict
conditional of [lewis-1973] against simplification of disjunctive antecedents, the inference
from a counterfactual with a disjunctive antecedent to the counterfactual from either
disjunct. Two arguments are stated on the substrate's variably strict conditional. The
bumper-crop argument: the English sentence is false while the disjunctive-closure reading
is true, so the sentence is regimented as the conjunction of the per-disjunct counterfactuals,
which is false as required. The Spain counterexample: *If Spain had fought on the Axis side
or the Allied side, Spain would have fought on the Axis side* is acceptable, yet
simplification would yield the absurd counterfactual from the Allied disjunct.

## Implementation notes

Both readings reduce to `Conditional.variablyStrictImp`, evaluated on the disjunction or
conjoined over the disjuncts, with propositions as sets of worlds of enumerated world types.
Similarity is a ranking of the worlds, so it is total as [lewis-1973]'s comparative similarity
requires, and with finitely many worlds each verdict is computed on the closest
antecedent-worlds (`holds`).

## References

* [mckay-vaninwagen-1977]
* [lewis-1973]
-/

@[expose] public section


namespace McKayVanInwagen1977

open Conditional

/-- On a ranking of finitely many worlds the variably strict conditional is the conditional of
the closest antecedent-worlds. -/
theorem holds {W : Type*} [Finite W] {α : Type*} [LinearOrder α] (d : W → W → α)
    (p q : Set W) :
    variablyStrictImp (fun w ↦ Preorder.lift (d w)) p q =
      closestImp (fun w ↦ Preorder.lift (d w)) p q :=
  (closestImp_eq_variablyStrictImp_of_finite (fun w ↦ Preorder.total_lift (d w)) p.toFinite).symm

/-!
## The Bumper Crop Argument

The critics argue that Lewis's semantics is wrong using the sentence:

  S: "If we were to have good weather this summer or if the sun were to
      grow cold, we would have a bumper crop."

They claim S is equivalent to the regimented counterfactual
S* = (goodWeather ∨ sunCold) > bumperCrop. Since Lewis's semantics
makes S* true (the closest (goodWeather ∨ sunCold)-world has good
weather, hence bumper crop) but S is clearly false, Lewis must be wrong.

McKay & Van Inwagen's rebuttal: premise (2) is false — S is NOT
equivalent to S*. The correct regimentation of S is the conjunction
(goodWeather > bumperCrop) ∧ (sunCold > bumperCrop), which IS false on
Lewis's semantics, matching the English judgment.
-/

section BumperCrop

inductive CropWorld where | actual | goodWeather | sunCold
  deriving Repr, DecidableEq

instance : Fintype CropWorld where
  elems := {.actual, .goodWeather, .sunCold}
  complete x := by cases x <;> simp

/-- A good-weather world is more like the actual world than any world in which the sun grows
    cold, which the paper takes to be "surely true". -/
def cropRank : CropWorld → ℕ
  | .actual => 0
  | .goodWeather => 1
  | .sunCold => 2

/-- Similarity to the actual world, by rank. -/
abbrev cropSim (_ : CropWorld) : Preorder CropWorld := Preorder.lift cropRank

/-- The good-weather worlds. -/
abbrev goodWeather : Set CropWorld := {.goodWeather}
/-- The worlds where the sun grows cold. -/
abbrev sunCold : Set CropWorld := {.sunCold}
/-- The bumper-crop worlds: the good-weather world. -/
abbrev bumperCrop : Set CropWorld := {.goodWeather}

/-- S* (Lewis disjunctive closure) is TRUE: the closest (goodWeather ∨ sunCold)-world is a
    good-weather world. This is premise (3) of the critics' argument. -/
theorem bumperCrop_lewis_true :
    .actual ∈ variablyStrictImp cropSim (goodWeather ∪ sunCold) bumperCrop := by
  rw [holds]; decide

theorem bumperCrop_conjunction_false :
    ¬ (.actual ∈ variablyStrictImp cropSim goodWeather bumperCrop ∧
       .actual ∈ variablyStrictImp cropSim sunCold bumperCrop) := by
  rw [holds, holds]; decide

/-- Lewis's disjunctive closure is true while the conjunction regimentation is false. Since
    the English sentence S is false (matching the conjunction) while S* is true (matching
    Lewis), S ≠ S*: premise (2) is false. -/
theorem lewis_ne_conjunction :
    .actual ∈ variablyStrictImp cropSim (goodWeather ∪ sunCold) bumperCrop ∧
    ¬ (.actual ∈ variablyStrictImp cropSim goodWeather bumperCrop ∧
       .actual ∈ variablyStrictImp cropSim sunCold bumperCrop) :=
  ⟨bumperCrop_lewis_true, bumperCrop_conjunction_false⟩

end BumperCrop

/-!
## The Spain Example

"Neither. Spain did not enter the war. But if she had fought on one side
or the other, it would have been the Axis."

That is, we assert: (Axis ∨ Allies) > Axis. This is true on Lewis's
semantics (Spain was ideologically closer to the Axis).

But if SDA were valid, it would follow that: Allies > Axis — "If Spain
had fought on the Allied side, Spain would have fought on the Axis side."
This is absurd.
-/

section Spain

inductive SpainWorld where | actual | axis | allies
  deriving Repr, DecidableEq

instance : Fintype SpainWorld where
  elems := {.actual, .axis, .allies}
  complete x := by cases x <;> simp

/-- Axis-worlds rank closer to actual than Allied ones: the paper asserts the counterfactual
    without stating an ordering, and this is the ranking that makes it true. -/
def spainRank : SpainWorld → ℕ
  | .actual => 0
  | .axis => 1
  | .allies => 2

/-- Similarity to the actual world, by rank. -/
abbrev spainSim (_ : SpainWorld) : Preorder SpainWorld := Preorder.lift spainRank

/-- The worlds where Spain fought with the Axis. -/
abbrev foughtAxis : Set SpainWorld := {.axis}
/-- The worlds where Spain fought with the Allies. -/
abbrev foughtAllies : Set SpainWorld := {.allies}

theorem spain_lewis_true :
    .actual ∈ variablyStrictImp spainSim (foughtAxis ∪ foughtAllies) foughtAxis := by
  rw [holds]; decide

theorem allies_implies_axis_false :
    .actual ∉ variablyStrictImp spainSim foughtAllies foughtAxis := by
  rw [holds]; decide

theorem sda_invalid :
    ∃ (W : Type) (ord : W → Preorder W) (A B C : Set W) (w : W),
      w ∈ variablyStrictImp ord (A ∪ B) C ∧ w ∉ variablyStrictImp ord B C :=
  ⟨SpainWorld, spainSim, foughtAxis, foughtAllies, foughtAxis, .actual,
   spain_lewis_true, allies_implies_axis_false⟩

end Spain

end McKayVanInwagen1977
