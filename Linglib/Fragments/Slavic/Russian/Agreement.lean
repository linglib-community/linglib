module

public import Linglib.Syntax.Agreement.Bundle
public import Linglib.Syntax.Agreement.Hierarchy
public import Linglib.Fragments.Slavic.Russian.Gender

/-!
# Russian agreement targets

Russian adjectives have a long form, declined for gender, number and case and used both
attributively and predicatively, and a short form, marked for gender and number and used
predicatively alone. Finite verbs express person and number in the nonpast tenses and gender
and number in the past tense. Each target's forms are tabulated in Wade's grammar.

## Implementation notes

Whether an inflected value is copied from a controller is a question about a position and is
left to the studies: a predicative long form is inflected for case, but its case is fixed by
the copula, nominative or instrumental, rather than shared with the subject. The witness
theorems read the inflection off the paradigms of `Fragments/Slavic/Russian/Gender.lean`.

## TODO

* The long adjective's full declension and the nonpast conjugation are not recorded, so the
  case and person dimensions have no witness theorem.

## References

* [wade-2020] — the adjective and the verb
* [corbett-1998] — Russian as the running example
-/

@[expose] public section

namespace Russian.Agreement

open _root_.Agreement

/-- The agreement targets of Russian whose forms a grammar tabulates are the long and the short
adjective and the nonpast and the past finite verb ([wade-2020]). -/
inductive Target where
  | longAdjective
  | shortAdjective
  | nonpastVerb
  | pastVerb
  deriving DecidableEq, Repr, Fintype

namespace Target

/-- A target's forms occupy positions of the Agreement Hierarchy: the long adjective is
attributive and predicative, the short adjective and the finite verb predicative only. -/
def positions : Target → Finset Position
  | .longAdjective => {.attributive, .predicate}
  | _ => {.predicate}

/-- A target's forms are inflected for dimensions: the long adjective declines for
gender, number and case, the short adjective for gender and number; the nonpast verb
expresses person and number, the past tense gender and number. -/
def features : Target → Finset Dimension
  | .longAdjective => {.gender, .number, .case}
  | .shortAdjective | .pastVerb => {.gender, .number}
  | .nonpastVerb => {.person, .number}

/-- The long adjective's nominative ending does not factor through its number: gender is
inflected. -/
theorem longAdjective_gender :
    ¬ Function.FactorsThrough
      (fun p : Gender.Value × Gender.numberSystem.values ↦ p.1.adjEnding p.2) Prod.snd := by
  decide

/-- Nor through its gender: number is inflected. -/
theorem longAdjective_number :
    ¬ Function.FactorsThrough
      (fun p : Gender.Value × Gender.numberSystem.values ↦ p.1.adjEnding p.2) Prod.fst := by
  decide

/-- The past-tense concord is not constant: gender is inflected. -/
theorem pastVerb_gender : ¬ Function.FactorsThrough Gender.Value.pastConcord (fun _ ↦ ()) := by
  decide

end Target

end Russian.Agreement
