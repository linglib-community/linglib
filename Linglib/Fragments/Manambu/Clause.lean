module

public import Mathlib.Data.Finset.Union
public import Linglib.Morphology.Morph
public import Linglib.Syntax.Clause.Chaining

/-!
# Manambu medial clauses

Manambu (Ndu, East Sepik Province, Papua New Guinea) chains medial clauses before one main
clause, marking the medial verb with one of nine suffixes. Seven mark switch-reference: the
completives *-ku* (same subject) and *-k* (different subject) 'after', also read as reason or real
condition, *-ta:y-kǝb* and *-kǝb* 'as soon as', and the same-subject *-ta:y* 'while', *-taka*
'immediately after' and *-ga:y* 'if', an unlikely condition. *-lǝk* 'because' and *-n*, sequence,
simultaneity or manner, are neutral. The verb before a marker is uninflected, partially inflected
with subject cross-referencing (*-k*, *-kǝb*), or fully inflected with tensed cross-referencing
(*-lǝk*). The completive auxiliary *napa-* carries the marker after a verb in *-n*, and the clause
keeps only its temporal readings.

## Main definitions

* `Manambu.MedialMarker`: the nine markers, with their switch-reference values, the relations
  they encode, the inflection of the verb before them and the columns of the grammar's table of
  medial clauses; they are a `Clause.Chaining.MedialForm`.
* `Manambu.MedialMarker.completiveRelations`: the relations of a medial clause with *napa-*.

## Implementation notes

The switch-reference values and relations are those of Aikhenvald's survey of the Ndu family
(Table 3), which gives *-ku* and *-k* one meaning and *-ta:y-kǝb* and *-kǝb* another; the grammar
describes *-ta:y-kǝb* by the meaning of *-ta:y* (§18.6) and pairs only *-ku* with *-k* (§18.1).
The verb type and the predicate, negation and *napa-* columns are the grammar's (Table 18.1),
where *-ta:y* and *-kǝb* also head a verbless predicate, which the survey reserves for *-n*. The
stand-alone clauses are the survey's (§9.2); the grammar also has desubordinated *-ta:y* and
*-kǝb* clauses (18.35, 18.47). The allomorphs *-tataka* and *-kǝkǝb* after a light root are not
represented. The grammar's account is checked in `Studies/Aikhenvald2008.lean`.

## References

* [aikhenvald-2008]
* [aikhenvald-2025]
-/

@[expose] public section

namespace Manambu

open Clause.Chaining Morphology

/-- *-ma:r-*, the negator of dependent clauses. -/
def dependentNegator : Morph := .suff "ma:r"

/-- *napa-*, the completive auxiliary of medial clauses. -/
def completive : Morph := .root "napa"

/-- The inflection of a medial verb before its marker. -/
inductive MedialInflection where
  /-- The verb is uninflected, a bare stem. -/
  | uninflected
  /-- The verb is partially inflected, with the subject cross-referencing of a dependent
  verb. -/
  | partiallyInflected
  /-- The verb is fully inflected, with the tensed subject cross-referencing of a main verb. -/
  | fullyInflected
  deriving DecidableEq, Repr, Fintype

/-- The markers of medial clauses, suffixes on the medial verb. -/
inductive MedialMarker where
  /-- *-ku* is the same-subject completive 'after', also read as reason or real condition. -/
  | ku
  /-- *-k* is the different-subject completive 'after', also read as reason or real
  condition. -/
  | k
  /-- *-ta:y* 'while' marks an action begun before the next clause's and overlapping it, with
  the same subject. -/
  | tay
  /-- *-taka*, *-tataka* after a light root, marks an action immediately followed by the next
  clause's, with the same subject. -/
  | taka
  /-- *-kǝb* 'as soon as', *-kǝkǝb* after a light root, marks an action immediately followed by
  the next clause's with a brief overlap, with a different subject. -/
  | keb
  /-- *-ta:y-kǝb* 'as soon as', the only bimorphemic marker, is the same-subject form of
  *-kǝb*. -/
  | taykeb
  /-- *-lǝk* 'because' marks a reason and is neutral to switch-reference. -/
  | lek
  /-- *-ga:y* 'if' marks an unlikely condition, with the same subject. -/
  | gay
  /-- *-n* marks a sequential or simultaneous action or a manner and is neutral to
  switch-reference. -/
  | n
  deriving DecidableEq, Repr, Fintype

namespace MedialMarker

/-- The morphs of a marker, after a heavy root. -/
def morphs : MedialMarker → List Morph
  | ku => [.suff "ku"]
  | k => [.suff "k"]
  | tay => [.suff "ta:y"]
  | taka => [.suff "taka"]
  | keb => [.suff "kǝb"]
  | taykeb => [.suff "ta:y", .suff "kǝb"]
  | lek => [.suff "lǝk"]
  | gay => [.suff "ga:y"]
  | n => [.suff "n"]

/-- The switch-reference value of a marker, `none` for *-lǝk* and *-n*. -/
def sr : MedialMarker → Option SwitchReference
  | ku | tay | taka | taykeb | gay => some .ss
  | k | keb => some .ds
  | lek | n => none

/-- The interclausal relations a marker encodes, one set for the two completives and one for the
two 'as soon as' markers. -/
def relations : MedialMarker → Finset InterclauseRelation
  | ku | k => {.sequential, .causal, .conditional}
  | tay => {.simultaneous}
  | taka => {.sequential}
  | keb | taykeb => {.sequential, .simultaneous}
  | lek => {.causal}
  | gay => {.conditional}
  | n => {.sequential, .simultaneous, .manner}

/-- The inflection of the verb before a marker. -/
def inflection : MedialMarker → MedialInflection
  | ku | tay | taka | taykeb | gay | n => .uninflected
  | k | keb => .partiallyInflected
  | lek => .fullyInflected

/-- The verb before the marker cross-references its subject. -/
def IndexesSubject (m : MedialMarker) : Prop := m.inflection ≠ .uninflected

instance : DecidablePred IndexesSubject := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The marked verb can head the predicate of a verbless clause. -/
def HeadsPredicate (m : MedialMarker) : Prop := m = n ∨ m = tay ∨ m = keb

instance : DecidablePred HeadsPredicate := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The medial clause can be negated and its verb repeated. -/
def Negatable (m : MedialMarker) : Prop := m ≠ gay

instance : DecidablePred Negatable := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The completive auxiliary *napa-* can carry the marker. -/
def WithCompletive (m : MedialMarker) : Prop := m ≠ taykeb ∧ m ≠ lek ∧ m ≠ gay

instance : DecidablePred WithCompletive := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A medial clause with the marker occurs on its own, as a command or with a resultative
sense. -/
def StandsAlone (m : MedialMarker) : Prop := m = ku ∨ m = n

instance : DecidablePred StandsAlone := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

instance : MedialForm MedialMarker where
  sr := sr
  relations := relations
  IndexesSubject := IndexesSubject

/-- The relations a medial clause encodes when *napa-* carries its marker, the temporal relations
of the marker. -/
def completiveRelations (m : MedialMarker) : Finset InterclauseRelation :=
  m.relations.filter InterclauseRelation.Temporal

end MedialMarker

end Manambu
