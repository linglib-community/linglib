module

public import Linglib.Core.Data.Setoid.Basic
public import Linglib.Syntax.Clause.Relative
public import Linglib.Fragments.German.Adjectives
public import Linglib.Fragments.German.Conjugation

/-!
# German relative clauses

This file defines the declension of the German relative pronoun *der* and the two German
relativizers. The relative pronoun takes its gender and number from its head and its case from its
role in the clause, which follows the head; a participle declined as an attributive adjective
forms a clause before the head. The declension is Durrell's, the relativized positions Keenan and
Comrie's.

## Main definitions

* `German.relativePronoun`: the declension of the relative pronoun.
* `German.relDer`, `German.relParticiple`: the two relativizers.

## Main results

* `German.relativePronoun_ne_definite_iff`: the relative pronoun departs from the definite article
  exactly in the genitive and in the dative plural (Durrell's Tables 4.1 and 5.8).
* `German.ker_relativePronoun_le_ker_definite`, `German.ker_relativePronoun_eq_ker_definite_iff`:
  it keeps apart every pair of cases the article keeps apart, and more only in the feminine
  singular.

## Implementation notes

Durrell reports *derer* for *deren* in the genitive plural and the genitive singular feminine, but
*deren* where a noun follows, as one follows a relativized possessor; only *deren* is recorded.

## References

* [durrell-2011]
* [keenan-comrie-1977]
* [keenan-comrie-1979]
-/

@[expose] public section

namespace German

open German.Case (forms)
open Determiners (definite)

/-- `relativePronoun x c` is the form of the relative pronoun with a head of gender and number `x`
in the case `c`. -/
def relativePronoun : GenderNumber → Case → String
  | .sg .masc => forms "der" "den" "dessen" "dem"
  | .sg .fem => forms "die" "die" "deren" "der"
  | .sg .neut => forms "das" "das" "dessen" "dem"
  | .pl => forms "die" "die" "deren" "denen"

/-- The relative pronoun declines as the definite article does except in the genitive and in the
dative plural. -/
theorem relativePronoun_ne_definite_iff (x : GenderNumber) (c : Case) :
    relativePronoun x c ≠ definite x c ↔ c = .gen ∨ x = .pl ∧ c = .dat := by
  revert x c; decide

theorem ker_relativePronoun_le_ker_definite (x : GenderNumber) :
    Setoid.ker (relativePronoun x) ≤ Setoid.ker (definite x) := by
  simp only [Setoid.le_def, Setoid.ker_def]; revert x; decide

/-- The relative pronoun distinguishes more cases than the definite article only in the feminine
singular. -/
theorem ker_relativePronoun_eq_ker_definite_iff (x : GenderNumber) :
    Setoid.ker (relativePronoun x) = Setoid.ker (definite x) ↔ x ≠ .sg .fem := by
  revert x; decide

/-- The relative pronoun *der*, in the case of the relativized position (*den Mann, den die Frau
schlägt* 'the man whom the woman is beating', [keenan-comrie-1979] p. 337), introduces a clause
after its head and relativizes every position but the object of comparison ([keenan-comrie-1977]
p. 74, Table 1 p. 77). -/
def relDer : Relativizer where
  placement := .postNominal
  realize
    | .subject | .directObject | .indirectObject | .oblique | .genitive => {.relPronoun}
    | _ => ∅

/-- A participle declined as an attributive adjective forms a clause before its head and
relativizes subjects only, the head being understood as the subject of the participle
([keenan-comrie-1977] p. 64). -/
def relParticiple : Relativizer where
  placement := .preNominal
  realize
    | .subject => {.gap}
    | _ => ∅

/-- The German relativizers. -/
def relativizers : List Relativizer := [relDer, relParticiple]

/-- [keenan-comrie-1977]'s (1) and (2), *der Mann, der in seinem Büro arbeitet* and *der in seinem
Büro arbeitende Mann* 'the man who is working in his study', built from the article and the
relative pronoun of the masculine *Mann*, the dative possessive of the neuter *Büro*, and the
present and the present participle of *arbeiten*, the participle with the ending of an adjective
after the article. -/
example :
    let arbeiten := Conjugation.weak "arbeiten"
    let seinem := Determiners.einWord "sein" (.sg .neut) .dat
    definite (.sg .masc) .nom ++ " Mann, " ++ relativePronoun (.sg .masc) .nom ++ " in " ++
        seinem ++ " Büro " ++ arbeiten.present = "der Mann, der in seinem Büro arbeitet" ∧
      definite (.sg .masc) .nom ++ " in " ++ seinem ++ " Büro " ++ arbeiten.presentParticiple ++
        Adjectives.ending .inflected (.sg .masc) .nom ++ " Mann" =
        "der in seinem Büro arbeitende Mann" := by
  decide

end German
