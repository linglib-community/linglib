module

public import Linglib.Data.Experiments.Schema

/-!
# CharnavelMateu2015: experimental results (generated)

Auto-generated from `Linglib/Data/Experiments/CharnavelMateu2015.json` by
`scripts/gen_experiments.py`. Do not edit by hand: edit the JSON and re-run the generator.

A grammaticality judgment task on French and Spanish clusters of a dative and a third-person
accusative clitic, crossing whether the accusative clitic's antecedent c-commands it, whether that
antecedent is a logophoric center, and the person of the dative clitic, which in one condition is a
third person bound by a quantifier. Ratings were given on a continuous scale, between subjects,
against control sentences with a full noun phrase as indirect object. Locators are to the pages of
the authors' accepted manuscript in Harvard's DASH repository.

## References

* [charnavel-mateu-2015]
-/

@[expose] public section

namespace CharnavelMateu2015

open Data.Experiments

/-- A yes or no entry of the condition tables. -/
inductive Answer where
  /-- yes: the condition has the property -/
  | yes
  /-- no: the condition lacks the property -/
  | no
  deriving DecidableEq, Repr, Fintype

/-- The person of the dative clitic. -/
inductive DativePerson where
  /-- 3: a free third-person dative clitic -/
  | third
  /-- 1/2: a first- or second-person dative clitic -/
  | participant
  /-- bound 3: a third-person dative clitic bound by a quantifier, as in (20) -/
  | boundThird
  deriving DecidableEq, Repr, Fintype

/-- The result of a condition. -/
inductive Grammaticality where
  /-- *: rated significantly lower than the control sentences -/
  | ungrammatical
  /-- OK: not rated significantly lower than the control sentences -/
  | ok
  deriving DecidableEq, Repr, Fintype

/-- Native speakers of French in the French version. (§2.2, p. 7; checked against the page
images.) -/
def frenchParticipants : ℕ := 97

/-- Native speakers of Spanish in the Spanish version. (§2.2, p. 7; checked against the page
images.) -/
def spanishParticipants : ℕ := 35

/-- Test items with clitic clusters. (§2.3, p. 7; checked against the page images.) -/
def testItems : ℕ := 27

/-- Control items with an accusative clitic and a full noun phrase as indirect object. (§2.3, p.
7; checked against the page images.) -/
def controlItems : ℕ := 6

/-- A row of Table 2, p. 9: the conditions of the task and their results, an asterisk marking a
condition rated significantly lower than the control sentences. -/
structure Result where
  /-- The condition's number. -/
  condition : ℕ
  /-- Whether the accusative clitic's antecedent c-commands it. -/
  cCommandingAntecedent : Answer
  /-- Whether the accusative clitic's antecedent is a logophoric center, an attitude holder
  introduced by an intensional predicate or expression (§2.3). -/
  logophoricAntecedent : Answer
  /-- The person of the dative clitic. -/
  dativePerson : DativePerson
  /-- The result. -/
  grammaticality : Grammaticality
  deriving DecidableEq, Repr

/-- The 9 rows of Table 2, p. 9, in the paper's order; checked against the page images. -/
def results : List Result :=
  [⟨1, .yes, .yes, .third, .ungrammatical⟩,
   ⟨2, .yes, .yes, .participant, .ok⟩,
   ⟨3, .yes, .yes, .boundThird, .ungrammatical⟩,
   ⟨4, .yes, .no, .third, .ok⟩,
   ⟨5, .yes, .no, .participant, .ok⟩,
   ⟨6, .no, .yes, .third, .ungrammatical⟩,
   ⟨7, .no, .yes, .participant, .ok⟩,
   ⟨8, .no, .no, .third, .ok⟩,
   ⟨9, .no, .no, .participant, .ok⟩]

end CharnavelMateu2015
