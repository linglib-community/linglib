module

public import Mathlib.Data.Finset.Union
public import Linglib.Data.UD.Features
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Clause.Chaining

/-!
# Korean converbs

Korean chains clauses with conjunctive suffixes, Sohn's term for its converbs, on the nonfinite
verb of each medial clause before a single final verb, without switch-reference. The nonfinite
verb keeps its voice, subject-honorific and tense slots but takes no sentence ender. *-go*
'and' coordinates, *-go(seo)*, *-eoseo*, *-jamaja* and *-daga* sequence events, *-myeonseo*
'while' marks simultaneity, *-eoseo*, *-(eu)ni* and *-(eu)nikka* give the reason,
*-(eu)myeon* 'if' conditions, *-jiman*, *-(eu)na* and *-eodo* concede, *-dorok* gives a
result or limit, *-(eu)ryeogo* and *-(eu)reo* the purpose, *-neunde* background, and *-geona*
and *-deunji* 'or' disjoin. Tense before a suffix is relative to the final verb; some suffixes
admit the past *-eoss* and the modal *-gess* before them and others exclude both. The negative
adverbs and the negative verb occur in a medial clause, governed by the sentence type of the
final clause. Forms are in the Revised Romanization; Sohn writes *-ko*, *-e(se)*,
*-(u)myense*, *-(u)nikka*, *-ciman*, *-tolok*, *-(u)lyeko*, *-taka*, *-ca(maca)*, *-kena*.

## Implementation notes

* `AllowsTense` and `AllowsModal` follow the features Sohn attaches to each conjunctor and,
  for *-geona*, *-deunji* and *-jamaja*, which his list omits, the attachment statements of
  the National Institute of Korean Language's dictionary; Sohn marks *-tunci* as excluding
  the modal, which the dictionary admits in one of its senses.
* The clause-chaining typology over the converbs is in `Studies/SarvasyAikhenvald2025.lean`.

## References

* [sohn-1994]
* [sohn-1999]
* [nikl-2016]
-/

@[expose] public section

namespace Korean

open Morphology (Morph)

/-- The conjunctive suffixes. -/
inductive Converb where
  /-- *-go* 'and', the coordinative suffix, tense before it absolute or relative. -/
  | go
  /-- *-go(seo)* 'and then', the contracted temporal suffix, also the manner, *malaeul
  tagoseo* 'riding a horse'. -/
  | goseo
  /-- *-myeonseo* 'while', the two events overlapping; the past before it when the medial
  event comes first. -/
  | myeonseo
  /-- *-eoseo* 'and then, so, by', the sequence, cause or manner; no past before it. -/
  | eoseo
  /-- *-(eu)myeon* 'if, when', taking the past for hypothetical readings. -/
  | myeon
  /-- *-jiman* 'but, although'. -/
  | jiman
  /-- *-(eu)na* 'but', the formal concessive. -/
  | na
  /-- *-eodo* 'although, even if, no matter'. -/
  | eodo
  /-- *-dorok* 'so that, to the extent that, until', a result, extent or temporal limit; no
  past before it. -/
  | dorok
  /-- *-(eu)nikka* 'because, as, since, when', the reason as the speaker presents it. -/
  | nikka
  /-- *-(eu)ni* 'since, as, after'. -/
  | ni
  /-- *-neunde* 'given that, and, but', supplying background. -/
  | neunde
  /-- *-(eu)ryeogo* 'intending to'. -/
  | ryeo
  /-- *-(eu)reo* 'in order to'. -/
  | reo
  /-- *-daga* 'and then, while', the transferentive, marking alternation when repeated. -/
  | daga
  /-- *-jamaja* 'as soon as'; no past before it. -/
  | jamaja
  /-- *-geona* 'or'. -/
  | geona
  /-- *-deunji* 'or', beside *-geona*. -/
  | deunji
  deriving DecidableEq, Repr, Fintype

namespace Converb

/-- The morphs of a converb. -/
def morphs : Converb → List Morph
  | go => [.suff "go"]
  | goseo => [.suff "go(seo)"]
  | myeonseo => [.suff "myeonseo"]
  | eoseo => [.suff "eoseo"]
  | myeon => [.suff "(eu)myeon"]
  | jiman => [.suff "jiman"]
  | na => [.suff "(eu)na"]
  | eodo => [.suff "eodo"]
  | dorok => [.suff "dorok"]
  | nikka => [.suff "(eu)nikka"]
  | ni => [.suff "(eu)ni"]
  | neunde => [.suff "neunde"]
  | ryeo => [.suff "(eu)ryeogo"]
  | reo => [.suff "(eu)reo"]
  | daga => [.suff "daga"]
  | jamaja => [.suff "jamaja"]
  | geona => [.suff "geona"]
  | deunji => [.suff "deunji"]

/-- The form of a converb in boundary notation. -/
def form (c : Converb) : String := Morph.surface c.morphs

/-- The gloss. -/
def gloss : Converb → String
  | go => "and"
  | goseo => "and then"
  | myeonseo => "while"
  | eoseo => "and then, so, by"
  | myeon => "if, when"
  | jiman => "but, although"
  | na => "but"
  | eodo => "although, even if"
  | dorok => "so that, to the extent that, until"
  | nikka => "because, as, since, when"
  | ni => "since, as, after"
  | neunde => "given that, and, but"
  | ryeo => "intending to"
  | reo => "in order to"
  | daga => "and then, while"
  | jamaja => "as soon as"
  | geona | deunji => "or"

/-- The interclausal relations a converb encodes. -/
def relations : Converb → Finset InterclauseRelation
  | go => {.additive}
  | goseo => {.sequential, .manner}
  | myeonseo => {.simultaneous}
  | eoseo => {.sequential, .causal, .manner}
  | myeon => {.conditional}
  | jiman | na | eodo => {.concessive}
  | dorok | ryeo | reo => {.purpose}
  | nikka => {.causal}
  | ni => {.causal, .sequential}
  | neunde => {.additive, .concessive}
  | daga => {.sequential, .simultaneous}
  | jamaja => {.sequential}
  | geona | deunji => ∅

/-- The past or perfect may be marked on the medial verb before the converb; before
*-myeonseo* only in its concessive reading. -/
def AllowsTense (c : Converb) : Prop :=
  c = go ∨ c = myeonseo ∨ c = myeon ∨ c = jiman ∨ c = na ∨ c = eodo ∨ c = nikka ∨ c = ni ∨
    c = neunde ∨ c = daga ∨ c = geona ∨ c = deunji

instance : DecidablePred AllowsTense :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

/-- The modal *-gess* may be marked on the medial verb before the converb; before
*-myeonseo* only in its concessive reading. -/
def AllowsModal (c : Converb) : Prop :=
  c = go ∨ c = myeonseo ∨ c = myeon ∨ c = jiman ∨ c = na ∨ c = nikka ∨ c = ni ∨ c = neunde ∨
    c = daga ∨ c = geona ∨ c = deunji

instance : DecidablePred AllowsModal :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

theorem allowsModal_imp_allowsTense (c : Converb) : c.AllowsModal → c.AllowsTense := by
  revert c; decide

/-- The verb form of a converb. -/
def verbForm (_ : Converb) : UD.VerbForm := .Conv

/-- The converbs as medial forms, neutral to switch-reference, encoding their relations, and
never indexing the subject. -/
instance : MedialForm Converb where
  sr _ := none
  relations := relations
  IndexesSubject _ := False

end Converb

end Korean
