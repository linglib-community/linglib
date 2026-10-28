module

public import Linglib.Semantics.Tense.Embedding
public import Mathlib.Data.Finset.Lattice.Fold
public import Linglib.Data.Examples.Ogihara1996

/-!
# Ogihara (1996): Tense, Attitudes, and Scope

[ogihara-1996] proposes a relative tense theory: a tense morpheme is interpreted in the scope of
the structurally higher tense, locating the time of its clause relative to the time of the tense
that commands it. English and Japanese share the theory and differ in two respects. English has
an absolute present, and it has a sequence-of-tense rule that optionally deletes a past tense
locally commanded by another past, leaving a null tense that is simultaneous with the commanding
time. Japanese has no such rule.

The tenses of a clause and the clauses embedded under it form a chain, and the readings of the
innermost clause are the positions its time may take against the outermost time, composed from
the cells of the relative tenses along the chain. A past under a past then has [the positions of
the Upper Limit Constraint where the rule applies and the past positions
alone](##readings_past_past) otherwise, so [it is simultaneous exactly in
English](##eq_mem_readings_past_past_iff), while a Japanese present under a past is simultaneous
and never shifted. The perfect is a relative past, and [a past perfect under a past places its
event before the commanding time](##readings_pastPerfect) however the rule applies, which is how
it can be used as a preterit. Because the rule deletes only a past whose local commander is a
past, [a past under a future stays a past](##readings_future_past) even beneath a higher past. The
book's sentences [have exactly the readings the chain allows](##rows_readings).

## Implementation notes

* A reading is a position of the innermost time against the commanding time, at the granularity
  of the cells of `Semantics/Tense/Defs.lean`. The book's intensional logic, in which tenses are
  quantifiers over times and attitude verbs relate individuals to sets of world-time pairs read
  de se, is not encoded; the null tense left by the rule is the property of times the attitude
  evaluates at its own time.
* The SOT rule applies to the underlying structure: whether a past is deleted depends on the
  morpheme that commands it before deletion.
* The Japanese present is a relative present and a relative future. The rows judge only the
  simultaneous and the shifted readings, so the future reading of a Japanese present under a past
  is predicted but untested.

## TODO

The English absolute present *-s* and the double-access sentences it gives under a past are not
encoded, nor are relative clauses, whose tenses the book interprets by NP scope as well as by the
rule.

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

/-- The relative tense morphemes of the book's chart of English and Japanese tenses. -/
inductive Morpheme
  /-- The English null tense `Ø`, a relative present. -/
  | null
  /-- The English past *-ed*. -/
  | ed
  /-- The English perfect *have*, a relative past. -/
  | perfect
  /-- The English future *woll*. -/
  | woll
  /-- The Japanese present *-(r)u*, a relative present and a relative future. -/
  | ru
  /-- The Japanese past *-ta*. -/
  | ta
  deriving DecidableEq, Fintype

namespace Morpheme

/-- The language of a morpheme. -/
def language : Morpheme → Language
  | ru | ta => .japanese
  | _ => .english

/-- The relative tenses the chart assigns a morpheme. -/
def tenses : Morpheme → Finset Tense
  | null => {.present}
  | ed => {.past}
  | perfect => {.past}
  | woll => {.future}
  | ru => {.present, .future}
  | ta => {.past}

/-- The cell of a morpheme: the positions its relative tenses allow the time of its clause
against the time of the tense commanding it. -/
def cell (m : Morpheme) : Finset Ordering := m.tenses.sup fun t ↦ ⟦t⟧

/-- A past tense morpheme, the target and trigger of the SOT rule. -/
def IsPastTense : Morpheme → Prop
  | ed | ta => True
  | _ => False

instance : DecidablePred IsPastTense
  | ed | ta => isTrue trivial
  | null | perfect | woll | ru => isFalse id

/-- The forms at LF of a morpheme `n` locally commanded by `m`: the SOT rule optionally deletes a
past tense locally commanded by another past, in a language that has the rule. -/
def forms (m n : Morpheme) : Finset Morpheme :=
  if m.IsPastTense ∧ n.IsPastTense ∧ n.language.HasSOT then {n, null} else {n}

end Morpheme

open Morpheme

/-- The past tense morpheme of a language. -/
def Language.past : Language → Morpheme
  | .english => ed
  | .japanese => ta

/-- The readings of a chain of tenses, each locally commanding the next: the positions of the
time of the last against the time of the first, composed from the cells of the forms at LF of each
tense against the tense above it. -/
def readings : List Morpheme → Finset Ordering
  | [] | [_] => ⟦present⟧
  | m :: n :: l => comp (readings (n :: l)) ((forms m n).sup cell)

/-- A past under a past takes the positions `pastUnderPast` of its language's SOT rule: before the
commanding time, or also at it where the rule applies. -/
theorem readings_past_past (L : Language) :
    readings [L.past, L.past] = pastUnderPast L.HasSOT := by
  cases L <;> decide

/-- A past under a past has a simultaneous reading exactly in a language with the SOT rule. -/
theorem eq_mem_readings_past_past_iff (L : Language) :
    .eq ∈ readings [L.past, L.past] ↔ L.HasSOT := by
  rw [readings_past_past, eq_mem_pastUnderPast_iff]

-- (2a), (10b)
theorem readings_japanese_present : .eq ∈ readings [ta, ru] ∧ .lt ∉ readings [ta, ru] := by
  decide

/-- A past perfect under a past places its event before the commanding time whether or not the
SOT rule deletes its past, the use of the perfect as a preterit. -/
theorem readings_pastPerfect : readings [ed, ed, perfect] = ⟦past⟧ := by decide

/-- A past under a future is not deleted, since its local commander is no past, so it stays
before the future time even when a past commands the future. -/
theorem readings_future_past : readings [woll, ed] = ⟦past⟧ ∧ readings [ed, woll, ed] = ⊤ := by
  decide

/-! ### The sentences -/

/-- A morpheme by its name in the rows. -/
def morpheme? (w : String) : Option Morpheme :=
  [("null", null), ("ed", ed), ("perfect", perfect), ("woll", woll), ("ru", ru),
    ("ta", ta)].lookup w

/-- The position a reading names: simultaneous, at the commanding time, or shifted, before it. -/
def reading? (w : String) : Option Ordering :=
  [("simultaneous", Ordering.eq), ("shifted", Ordering.lt)].lookup w

/-- The judged readings of the rows: the chain of tenses of each row, with the position each of
its readings names and the judgment of that reading. -/
def judged : List (List Morpheme × Ordering × Judgment) :=
  Examples.all.flatMap fun row ↦ ((row.features "tense").mapM morpheme?).toList.flatMap fun ms ↦
    row.readings.filterMap fun r ↦ (reading? r.1).map fun o ↦ (ms, o, r.2)

/-- Every reading of the book's sentences is acceptable exactly when the chain of its tenses
allows its position. -/
theorem rows_readings :
    (∀ x ∈ judged, (x.2.1 ∈ readings x.1 ↔ x.2.2 = .acceptable)) ∧ judged.length = 11 := by
  decide +kernel

end Ogihara1996
