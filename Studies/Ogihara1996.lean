module

public import Linglib.Semantics.Tense.Embedding
public import Mathlib.Data.Finset.Lattice.Fold
public import Linglib.Data.Examples.Ogihara1996
public import Linglib.Fragments.Japanese.Tense

/-!
# Ogihara (1996): Tense, Attitudes, and Scope

[ogihara-1996] interprets each tense relative to the time of the tense above it. English adds an
absolute present and a sequence-of-tense rule that optionally deletes a tense whose local tense
feature, the nearest [+past] or [+pres] above it, is its own, leaving a null tense at the
commanding time. A past under a past is then [simultaneous exactly in
English](##eq_mem_readings_past_past_iff), as is [a past under the
perfect](##readings_presentPerfect_past). Beneath a higher past, [a past perfect stays a
past](##readings_pastPerfect) and so does [a past under *will*](##readings_future_past), and the
book's sentences [have exactly these readings](##rows_readings).

## Implementation notes

* A reading is a position of the time of the innermost clause against the time of the clause
  above it, the utterance time for a matrix clause, at the granularity of the cells of
  `Semantics/Tense/Defs.lean`. The book's intensional logic, in which tenses are
  quantifiers over times and attitude verbs relate individuals to sets of world-time pairs read
  de se, is not encoded; the null tense left by the rule is the property of times the attitude
  evaluates at its own time.
* The SOT rule is the book's definitive version, over the tense features [+past] and [+pres]:
  the pasts and the perfect carry [+past], the presents [+pres], and the null tense and *woll*
  none that the rule sees. A morpheme's local tense feature is that of the nearest morpheme above
  it to carry one, read off the structure before deletion. A tense is deleted with its feature;
  the rule names the perfect beside the tenses, so deleting its feature leaves the perfect in
  place, changes no reading, and the perfect acts as a trigger only.
* The English absolute present *-s* enters a chain for its [+pres] feature, by which the present
  of *will* keeps a past below it from being deleted under a higher past
  (`lf_past_future_past`). Its cell is the present: as the tense of a matrix clause it is the
  utterance time, so a past under it [precedes the commanding time](##readings_present_past).
  Under a past the cell reads it as a relative present, standing in for the double-access reading
  the book gives it.
* The Japanese present *-(r)u* and past *-ta* have the tenses their verbal endings mark in
  `Japanese.Tense.ending`, where the present and the future share the non-past, and *-(r)u*
  [stands for the non-past of every conjugation](##Morpheme.tenses_ru), the copula *-da* among
  them. The rows judge only the simultaneous and the shifted readings, so the future reading of a
  Japanese present under a past is predicted but untested.

## Errata

The note to the chart of tenses says that the English present *-s* surfaces only with a first
person singular subject; it is the third person singular.

## TODO

The interpretation of the English absolute present *-s* and the double-access sentences it gives
under a past are not encoded, nor are relative clauses, whose tenses the book interprets by NP
scope as well as by the rule, nor the common nouns that carry tense features and trigger the rule
in their complements.

## References

* [ogihara-1996]
-/

@[expose] public section

namespace Ogihara1996

open Tense
open scoped Denotes

/-- The two languages compared. -/
inductive Language
  | english
  | japanese
  deriving DecidableEq

/-- A language has the sequence-of-tense rule: English does, Japanese does not. -/
def Language.HasSOT : Language → Prop
  | .english => True
  | .japanese => False

instance : DecidablePred Language.HasSOT
  | .english => isTrue trivial
  | .japanese => isFalse id

/-- The tense features that the SOT rule sees, [+past] and [+pres]. -/
inductive Feature
  | past
  | pres
  deriving DecidableEq

/-- The tense morphemes of the book's chart of English and Japanese tenses. -/
inductive Morpheme
  /-- The English present *-s*, an absolute present. -/
  | s
  /-- The English null tense `Ø`, a relative present. -/
  | null
  /-- The English past *-ed*. -/
  | ed
  /-- The English perfect *have*, a relative past. -/
  | perfect
  /-- The English future *woll*. -/
  | woll
  /-- The Japanese present *-(r)u*, the non-past. -/
  | ru
  /-- The Japanese past *-ta*. -/
  | ta
  deriving DecidableEq, Fintype

namespace Morpheme

/-- The language of a morpheme. -/
def language : Morpheme → Language
  | ru | ta => .japanese
  | _ => .english

/-- The tenses the chart assigns a morpheme, a Japanese one the tenses whose verbal ending it
is. -/
def tenses : Morpheme → Finset Tense
  | s | null => {.present}
  | ed => {.past}
  | perfect => {.past}
  | woll => {.future}
  | ru => {t | Japanese.Tense.ending .verbal t = Japanese.Verb.Exponent.u.morphs}
  | ta => {t | Japanese.Tense.ending .verbal t = Japanese.Verb.Exponent.ta.morphs}

/-- The cell of a tense morpheme: the positions its tenses allow its time against the time of the
tense commanding it. -/
def cell (m : Morpheme) : Finset Ordering := m.tenses.sup fun t ↦ ⟦t⟧

-- p. 2: *-(r)u* stands for the non-past ending of every predicate, the copula's among them.
theorem tenses_ru (c : Japanese.Tense.Conjugation) :
    ru.tenses =
      ({t | Japanese.Tense.ending c t = Japanese.Tense.ending c .present} : Finset _) := by
  ext t
  simp only [tenses, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (Japanese.Tense.ending_eq_ending_iff (t' := .present) .verbal).trans
    (Japanese.Tense.ending_eq_ending_iff c).symm

/-- The tense feature a morpheme carries: [+past] for the pasts and the perfect, [+pres] for the
presents, and none that the SOT rule sees for the null tense and *woll*. -/
def feature : Morpheme → Option Feature
  | ed | ta | perfect => some .past
  | s | ru => some .pres
  | null | woll => none

/-- A tense morpheme, deleted with its feature by the SOT rule. The perfect carries a feature
without being a tense, and the null tense is what deletion leaves. -/
def IsTense : Morpheme → Prop
  | s | ed | ru | ta => True
  | null | perfect | woll => False

instance : DecidablePred IsTense
  | s | ed | ru | ta => isTrue trivial
  | null | perfect | woll => isFalse id

/-- (67): the forms at LF of a morpheme `n` whose local tense feature is `φ`. The SOT rule
optionally deletes a tense whose local tense feature is its own, in a language that has the
rule, leaving the null tense. -/
def forms (φ : Option Feature) (n : Morpheme) : Finset Morpheme :=
  if n.IsTense ∧ n.feature = φ ∧ n.language.HasSOT then {n, null} else {n}

end Morpheme

open Morpheme

/-- The tense morphemes of a tense form in a language, outermost first. In English these are the
tense inflection, *-ed* or *-s*, the perfect for a past participle under *have* and *woll* for an
infinitive under *will*; the present participle, an aspect, contributes none. In Japanese the
morpheme is the ending of the finite tense, *-ta* or *-(r)u*. -/
def Morpheme.ofForm : Language → Form → List Morpheme
  | .english, f =>
    (match f.finite with | .past => [ed] | .present => [s] | .future => []) ++
      f.nonfinite.filterMap fun
        | .pastParticiple => some perfect
        | .infinitive => some woll
        | .presentParticiple => none
  | .japanese, f => [if f.finite ∈ ta.tenses then ta else ru]

/-- The tense morphemes of the clauses of a sentence, outermost first, each clause's tense form
read in the language. -/
def chain (L : Language) (fs : List Form) : List (List Morpheme) := fs.map (Morpheme.ofForm L)

/-- The forms at LF of a sequence of morphemes, each locally commanding the next, when the local
tense feature of the first is `φ`: a morpheme passes its own feature, if it carries one, to the
morphemes below it. -/
def lf (φ : Option Feature) : List Morpheme → List (Finset Morpheme)
  | [] => []
  | m :: l => forms φ m :: lf (m.feature.or φ) l

/-- The composite of a chain of cells, each against the time above it: the positions of the time
of the last against the time above the first. -/
def compAlong : List (Finset Ordering) → Finset Ordering
  | [] => ⟦present⟧
  | C :: cs => comp (compAlong cs) C

/-- The readings of a sentence, given the tense morphemes of its clauses: the positions of the
time of its last clause against the time of the clause above it, composed from the cells of the
last clause's morphemes at LF. The clause above a matrix clause is the utterance. -/
def readings (cs : List (List Morpheme)) : Finset Ordering :=
  compAlong (((lf none cs.flatten).drop cs.dropLast.flatten.length).map (·.sup cell))

/-- A past under a past takes the positions `pastUnderPast` of its language's SOT rule: before the
commanding time, or also at it where the rule applies. -/
theorem readings_past_past (L : Language) :
    readings (chain L [.simplePast, .simplePast]) = pastUnderPast L.HasSOT := by
  cases L <;> decide

theorem eq_mem_readings_past_past_iff (L : Language) :
    .eq ∈ readings (chain L [.simplePast, .simplePast]) ↔ L.HasSOT := by
  rw [readings_past_past, eq_mem_pastUnderPast_iff]

-- (2a), (10b)
theorem readings_japanese_present :
    .eq ∈ readings (chain .japanese [.simplePast, .simplePresent]) ∧
      .lt ∉ readings (chain .japanese [.simplePast, .simplePresent]) := by
  decide

-- a matrix present is the utterance time, in English as in Japanese
theorem readings_present_past (L : Language) :
    readings (chain L [.simplePresent, .simplePast]) = ⟦past⟧ := by
  cases L <;> decide

/-- A past perfect under a past places its event before the commanding time whether or not the
SOT rule deletes its past, the use of the perfect as a preterit. -/
theorem readings_pastPerfect : readings (chain .english [.simplePast, .pastPerfect]) = ⟦past⟧ := by
  decide

/-- A past under the perfect, as in *John has said that Mary was sick*, has the simultaneous
reading as a past under a past does, before or at the time of the saying, since the perfect
carries [+past] and triggers the rule. -/
theorem readings_presentPerfect_past :
    readings (chain .english [.presentPerfect, .simplePast]) = upperLimitConstraint := by
  decide

/-- A past under a future is not deleted, since its local tense feature is the [+pres] of
*will*, so it stays before the future time even when a past commands the future. Without that
present, the higher past would license deletion and the simultaneous reading. -/
theorem readings_future_past :
    readings (chain .english [.future, .simplePast]) = ⟦past⟧ ∧
      readings (chain .english [.simplePast, .future, .simplePast]) = ⟦past⟧ ∧
      readings [[ed], [woll], [ed]] = upperLimitConstraint := by
  decide

-- the [+pres] of *will* is the lowest past's local tense feature, so the rule cannot delete it
theorem lf_past_future_past :
    lf none (chain .english [.simplePast, .future, .simplePast]).flatten =
        [{ed}, {s}, {woll}, {ed}] ∧
      lf none [ed, woll, ed] = [{ed}, {woll}, {ed, null}] := by
  decide

/-! ### The sentences -/

/-- The language of a row, by its Glottocode. -/
def language? (g : String) : Option Language :=
  [("stan1293", Language.english), ("nucl1643", .japanese)].lookup g

/-- A tense form by its name in the rows. -/
def form? (w : String) : Option Form :=
  [("simplePast", Form.simplePast), ("simplePresent", .simplePresent), ("future", .future),
    ("pastPerfectProgressive", Form.pastProgressive.perfect)].lookup w

/-- The position a reading names: simultaneous, at the commanding time, or shifted, before it. -/
def reading? (w : String) : Option Ordering :=
  [("simultaneous", Ordering.eq), ("shifted", Ordering.lt)].lookup w

/-- The tense morphemes of the clauses of a row, from their forms in its language. -/
def chain? (row : Datum) : Option (List (List Morpheme)) := do
  pure (chain (← language? row.language) (← (row.features "form").mapM form?))

/-- The judged readings of the rows: the clauses of each row, with the position each of its
readings names and the judgment of that reading. -/
def judged : List (List (List Morpheme) × Ordering × Judgment) :=
  Examples.all.flatMap fun row ↦ (chain? row).toList.flatMap fun ms ↦
    row.readings.filterMap fun r ↦ (reading? r.1).map fun o ↦ (ms, o, r.2)

/-- Every row's forms and readings are read, and every reading of the book's sentences is
acceptable exactly when the rule allows its position. -/
theorem rows_readings :
    (∀ row ∈ Examples.all, (chain? row).isSome ∧ ∀ r ∈ row.readings, (reading? r.1).isSome) ∧
      ∀ x ∈ judged, (x.2.1 ∈ readings x.1 ↔ x.2.2 = .acceptable) := by
  decide +kernel

end Ogihara1996
