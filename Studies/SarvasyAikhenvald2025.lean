module

public import Linglib.Fragments.Korean.Clause
public import Linglib.Fragments.Manambu.Clause
public import Linglib.Fragments.Nungon.Clause
public import Linglib.Fragments.Turkish.Clause
public import Linglib.Semantics.ClauseLinking
public import Linglib.Syntax.Clause.Chaining
public import Studies.Aikhenvald2009
public import Studies.Sohn2009
public import Studies.Stassen1985

/-!
# Sarvasy & Aikhenvald (2025): Clause Chaining in the Languages of the World

The introduction to the volume defines a clause chain as one or more medial clauses, whose verbal
predicates are formally dependent and usually underspecified for tense, mood, modality or
polarity, combined with a single clause whose predicate has the form of an independent clause's;
the medial clauses are dependent without being embedded, and any lexical verb may occur anywhere
in the chain. The independent clause comes last in a language of verb-final order and first
otherwise, the medial-final and initial-medial orders of chaining (`Order`). The introduction then
surveys how chaining varies, and this file checks its generalizations on the medial forms of four
languages, Nungon and Manambu of New Guinea and Korean and Turkish:

* many medial-final languages of New Guinea and the Americas mark switch-reference on medial
  verbs and the chaining languages of Eurasia mostly do not (`marksSwitchReference`), and a
  same-subject medial verb marks fewer categories than a different-subject one, leaving the
  person of the subject unmarked (`indexesSubjectIffDS`);
* a medial verb may bear a tense marker of independent verbs with the meaning of a relative
  tense, as in Korean, where tense is found before some medial suffixes (`korean_tense`);
* the clauses of a chain may in most languages be negated one by one, while a few languages have
  medial forms that cannot be (`negated_individually`);
* where a language has several medial forms, the most basic ones mark the temporal relations of
  a sequence of events, succession and simultaneity (`succession_and_relativeTime_marked`).

## Implementation notes

The Korean and Turkish inventories come from reference grammars rather than the volume. The
introduction's labels for the commonest Turkish medial suffixes are rendered as Dixon's kinds of
clause linking, to which it refers the semantics of medial clauses: sequential is temporal
succession, temporal and simultaneous are relative time, and 'integrative' is not rendered.

## TODO

The three patterns of absolute tense on medial verbs and the scope of mood over a chain have no
language in the sample to be checked on. The two bridging constructions, recapitulative and
summary linkage, and the medial clauses that stand alone are not formalized, nor is the
introduction's statement that Nungon's two medial verbs each allow succession, addition,
causation and conditionality.

## References

* [sarvasy-aikhenvald-2025]
* [stassen-1985]
* [dixon-2009]
* [aikhenvald-2009]
* [sohn-2009]
-/

@[expose] public section

namespace SarvasyAikhenvald2025

open Clause

/-! ### The order of a chain -/

/-- The order of a clause chain, by the place of its one independent clause. -/
inductive Order where
  /-- The independent clause is last, as in languages of verb-final order. -/
  | medialFinal
  /-- The independent clause is first, as in languages of verb-initial or verb-medial order. -/
  | initialMedial
  deriving DecidableEq, Repr, Fintype

/-- Stassen's type of temporal chaining for an order: anterior consecutive deranking for the
medial-final order and posterior consecutive deranking for the initial-medial one. -/
def Order.chainType : Order → Stassen1985.ChainType
  | .medialFinal => .absolute .lt
  | .initialMedial => .absolute .gt

theorem Order.temporality_chainType (o : Order) : o.chainType.temporality = .consecutive := by
  cases o <;> rfl

/-! ### Switch-reference -/

/-- Of the four languages the two of New Guinea mark switch-reference on medial verbs and the
two of Eurasia do not. -/
theorem marksSwitchReference :
    MedialForm.MarksSwitchReference Nungon.Medial ∧
      MedialForm.MarksSwitchReference Manambu.MedialMarker ∧
      ¬ MedialForm.MarksSwitchReference Korean.Converb ∧
      ¬ MedialForm.MarksSwitchReference Turkish.Converb := by
  decide

/-- In Nungon and Manambu a medial verb marked for switch-reference indexes its subject exactly
when the subject of the next clause differs. -/
theorem indexesSubjectIffDS :
    MedialForm.IndexesSubjectIffDS Nungon.Medial ∧
      MedialForm.IndexesSubjectIffDS Manambu.MedialMarker := by
  decide

/-! ### Tense and polarity -/

/-- Tense may precede the Korean medial suffixes of circumstance or contrast, of an interrupted
event, of reason and of general sequence, and it may not precede every medial suffix. -/
theorem korean_tense :
    (∀ c ∈ [Korean.Converb.neunde, .daga, .nikka, .go], c.AllowsTense) ∧
      ∃ c : Korean.Converb, ¬ c.AllowsTense := by
  decide

/-- Every Turkish medial clause can be negated on its own, and every Manambu one but that of a
single marker. -/
theorem negated_individually :
    (∀ c : Turkish.Converb, c.Negatable) ∧
      ∃ m : Manambu.MedialMarker, ¬ m.Negatable ∧ ∀ m', ¬ m'.Negatable → m' = m := by
  decide

/-! ### The semantics of medial clauses -/

/-- The commonest Turkish medial suffixes with the kinds of linking the introduction gives them:
sequential *-Ip*, temporal *-ElI* 'since', manner *-ErEk* 'by doing', temporal or causal
*-IncE* 'when', simultaneous *-ken* 'while', temporal *-Er … -mEz* 'as soon as' and manner
*-E … -E*. -/
def turkishLinkings : List ((Turkish.Converb ⊕ Turkish.DoubledConverb) × Finset Linking) :=
  [(.inl .ip, {.succession}), (.inl .ali, {.relativeTime}), (.inl .arak, {.realManner}),
    (.inl .inca, {.relativeTime, .cause}), (.inl .ken, {.relativeTime}),
    (.inr .arMaz, {.relativeTime}), (.inr .aA, {.realManner})]

/-- Manambu, Korean and Turkish each have a medial form for temporal succession and one for
relative time. -/
theorem succession_and_relativeTime_marked :
    (∀ l ∈ [Linking.succession, .relativeTime], ∃ m, l ∈ Aikhenvald2009.linkings m) ∧
      (∀ l ∈ [Linking.succession, .relativeTime], ∃ c, l ∈ Sohn2009.linkings c) ∧
      ∀ l ∈ [Linking.succession, .relativeTime], ∃ r ∈ turkishLinkings, l ∈ r.2 := by
  decide

end SarvasyAikhenvald2025
