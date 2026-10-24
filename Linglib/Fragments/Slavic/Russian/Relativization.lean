module

public import Linglib.Syntax.Clause.Relative
public import Linglib.Fragments.Slavic.Russian.Agreement

/-!
# Russian relative clauses

This file defines the declension of the Russian relative pronoun *kotoryj* and the Russian
relativizer. The relative pronoun agrees with its head in gender and number, takes its case from
its role in the clause, and declines as a hard-stem adjective. The declension is Wade's, the
relativized positions Keenan and Comrie's.

## Main definitions

* `Russian.relativePronoun`: the declension of the relative pronoun.
* `Russian.relKotoryj`: the relativizer.

## Main results

* `Russian.relativePronoun_nom_eq_acc_iff`: the relative pronoun has one form for the nominative
  and the accusative exactly in the neuter singular and, with an inanimate head, outside the
  feminine singular.

## Implementation notes

Keenan and Comrie mention a participial strategy that relativizes subjects only (p. 70) but do not
enter it in Table 1; it is not recorded.

## References

* [wade-2020]
* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace Russian

open Russian.Agreement (longEnding)

/-- `relativePronoun g a n c` is the form of the relative pronoun with a head of gender `g`,
subgender `a` and number `n` in the case `c`, the stem *kotor-* with the endings of a hard-stem
adjective ([wade-2020] §121, §123). -/
def relativePronoun (g : Gender.Value) (a : Gender.Animacy) (n : Gender.numberSystem.values)
    (c : Case) : String :=
  "kotor" ++ (longEnding g a n c).form

/-- The relative pronoun has one form for the nominative and the accusative exactly in the neuter
singular and, with an inanimate head, outside the feminine singular. -/
theorem relativePronoun_nom_eq_acc_iff (g : Gender.Value) (a : Gender.Animacy)
    (n : Gender.numberSystem.values) :
    relativePronoun g a n .nom = relativePronoun g a n .acc ↔
      g = .neut ∧ n = Gender.numberSystem.value .singular ∨
        a = .inanimate ∧ (g ≠ .fem ∨ n = Gender.numberSystem.value .plural) := by
  revert g a n; decide

/-- The relative pronoun *kotoryj*, in the case of the relativized position, introduces a clause
after its head and relativizes every position but the object of comparison ([keenan-comrie-1977]
Table 1 p. 78). -/
def relKotoryj : Relativizer where
  placement := .postNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique | .genitive => {.relPronoun}
    | _ => ∅

/-- The Russian relativizers. -/
def relativizers : List Relativizer := [relKotoryj]

/-- [keenan-comrie-1977]'s (5), *devuška, kotoruju Džon ljubit* 'the girl who John likes' against
*devuška, kotoraja ljubit Džona* 'the girl who likes John' (pp. 65–66), and [keenan-comrie-1979]'s
(87) and (88) (p. 344), with the feminine animate *devuška*. -/
example :
    relativePronoun .fem .animate (Gender.numberSystem.value .singular) .acc = "kotoruju" ∧
      relativePronoun .fem .animate (Gender.numberSystem.value .singular) .nom = "kotoraja" := by
  decide

end Russian
