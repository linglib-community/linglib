module

public import Mathlib.Data.Fintype.Card
public import Linglib.Core.Order.UpperLower.Finset
public import Linglib.Syntax.Gender.Basic

/-!
# Feature decomposition of gender

This file defines the bivalent features [±feminine] and [±neuter] of a sex-based three-gender
system. Neuter is the most specified gender and masculine the least, as in the person and number
presentations.

## Main definitions

* `Gender.Features`: the bivalent [±feminine, ±neuter] features as finsets over the chain
  feminine < neuter, whose well-formed cells are `Features.neuter`, `Features.feminine` and
  `Features.masculine`.

## Implementation notes

* The bivalent presentation's three-cell bound `Features.card_wellFormed` is a claim about
  the presentation and not about gender systems: Fula has twenty controller genders.
* Smith's dual-feature system is `Minimalist.DualFeature.Bundle`, and Kramer's gender features
  on the nominal categorizer are in `Morphology/DistributedMorphology/Gender.lean`.
* Hammerly's rejection of the presentation, with masculine a bare gender node and natural
  gender derived at LF, is a single-paper analysis for its study.

## References

* [sauerland-2003] — the markedness ordering the bivalent presentation reconstructs
* [sauerland-2008b] — the Dominance test for markedness
* [hammerly-2019]
-/

@[expose] public section

namespace Gender

/-! ### The bivalent presentation: [±feminine, ±neuter]

[sauerland-2003] derives Czech gender agreement under coordination from a markedness ordering on
which masculine is semantically vacuous, feminine presupposes non-masculinity and neuter
presupposes genderlessness (§6, (45)); [sauerland-2008b]'s Dominance test, the gender a mixed
coordination takes, likewise makes masculine less marked than feminine (pp. 63–65). The
presentation here reconstructs the ordering as two binary features with the containment
[+neuter] → [+feminine], so the three genders of a sex-based system are the initial segments of
the chain feminine < neuter, neuter the most specified and masculine the least, as for person and
number (`Person.Features`, `Number.Features`). -/

/-- The two gender features, neuter depending on feminine. -/
inductive Feature where
  /-- [feminine] holds of non-masculine referents, those feminine and neuter share. -/
  | feminine
  /-- [neuter] holds of referents triggering neuter agreement. -/
  | neuter
  deriving DecidableEq, Repr, Fintype

/-- `Feature.rank` places feminine below neuter on the dependency chain. -/
def Feature.rank : Feature → Fin 2
  | .feminine => 0
  | .neuter => 1

instance : LinearOrder Feature := LinearOrder.lift' Feature.rank (by decide)

instance : LocallyFiniteOrderBot Feature := Fintype.toLocallyFiniteOrderBot

/-- A gender feature bundle is the set of its positive features. -/
abbrev Features := Finset Feature

open Finset in
/-- The neuter is [+feminine, +neuter], the whole chain. -/
def Features.neuter : Features := Iic .neuter

open Finset in
/-- The feminine is [+feminine, −neuter], the chain below neuter. -/
def Features.feminine : Features := Iic .feminine

/-- The masculine is [−feminine, −neuter], the empty bundle. -/
def Features.masculine : Features := ∅

theorem Features.neuter_eq : Features.neuter = {.feminine, .neuter} := by decide

theorem Features.feminine_eq : Features.feminine = {.feminine} := by decide

theorem Features.not_wellFormed_singleton_neuter :
    ¬ IsLowerSet (↑({.neuter} : Features) : Set Feature) := by
  decide

theorem Features.card_wellFormed :
    Fintype.card {gf : Features // IsLowerSet (↑gf : Set Feature)} = 3 := by
  rw [Fintype.card_subtype_isLowerSet]; rfl

/-- Map gender features to the comparative labels. -/
def Features.toGender (f : Features) : Option Label :=
  if .neuter ∈ f then if .feminine ∈ f then some .neuter else none
  else if .feminine ∈ f then some .feminine else some .masculine

/-- Map comparative labels to gender features (partial — only sex-based
    labels have feature equivalents). -/
def Features.fromGender : Label → Option Features
  | .neuter    => some Features.neuter
  | .feminine  => some Features.feminine
  | .masculine => some Features.masculine
  | _          => none

theorem Features.fromGender_toGender {f : Features} (h : IsLowerSet (↑f : Set Feature)) :
    f.toGender.bind Features.fromGender = some f := by
  revert f; decide

end Gender
