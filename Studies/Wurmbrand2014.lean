module

public import Mathlib.Algebra.Order.Ring.Int
public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Aspect.Viewpoint
public import Studies.Ogihara1996
public import Linglib.Data.Examples.Wurmbrand2014
public import Linglib.Data.Examples.Gloss
public import Linglib.Syntax.Minimalist.Linearization.Spellout
public import Linglib.Fragments.English.Auxiliaries
public import Linglib.Fragments.English.Verbs.Implicative
public import Linglib.Fragments.English.Verbs.Communication

/-!
# Wurmbrand (2014): Tense and Aspect in English Infinitives

Wurmbrand argues that English infinitives have no tense of their own. A future infinitive carries
the future modal *woll* without the present tense of *will*, so [its future is relative where
*will*'s is absolute](##orientation_rows), it is [no silent *would*](##not_silent_would), and [a
past below it can be simultaneous](##sot_rows). A simultaneous infinitive takes the attitude
holder's NOW or the matrix reference time as its reference time, and since perfective aspect puts
the event properly inside the reference time, [a bare episodic verb phrase is always possible in a
future infinitive, never in a propositional one, and in a tenseless one only under an extended
matrix reference time](##table3), as [the aspect rows bear out](##aspect_rows).

## Implementation notes

* The tense morphemes, their features and the SOT rule (23), which the paper adopts from Ogihara,
  are those of `Studies/Ogihara1996`: *will* is the present over *woll* and *would* the past over
  it, both read off `Tense.Form`, and a future infinitive is *woll* alone (21b). A reading is
  Ogihara's position of the deepest clause's time against the time of the clause above it.
* Ogihara's chains read the English present as relative, and (21a) needs it absolute, so the event
  times a clause allows (`Locates`) put the time below *-s* at the utterance time and the time
  below any other morpheme in that morpheme's cell. These times are points, as in the cells.
* Reference times are nonempty intervals. (47) prints the perfective with proper inclusion and the
  imperfective, Pancheva's `Aspect.UNBOUNDED`, with inclusion. The attitude holder's NOW and the
  utterance time, which the paper takes to be very short, are instants, which properly contain no
  run time, and an adverbial such as *at 5 p.m.* restricts a reference time to an instant (`D`).
  Statives project no aspect (p. 428). The evaluation time of *woll* and the NOW are one instant.
* Each row's class, matrix reference time and aspect are stated where it is paired. The
  sequence-of-tense rows run on linearized witnesses over a study lexicon that pronounce their
  sentences (`Minimalist.SpellsOut`), each chain read off the witness's pronounced tense items.

## TODO

* Table 4 assigns each verb its classes. Read from the attitudes of the English fragment, the
  preferential *decide*, *want*, *promise* and *expect* are its future verbs and the doxastic
  *believe* its propositional one, but the fragment gives *claim* no attitude, *expect* neither an
  infinitival frame nor its propositional reading (60), *begin* no infinitival frame and *seem* no
  attitude holder (70), so the rows state their classes.
* Ogihara's rule deletes the past of *would* optionally where the paper makes deletion obligatory,
  so the readings of (28b) are not paired; nor are the futurate progressive of (6e), the finite
  rows of (50), the double-access sentences of (58) and the embedded sequence of tense of (59).

## References

* [wurmbrand-2014]
* [ogihara-1996]
* [abusch-1988]
* [pancheva-von-stechow-2004]
* [wurmbrand-2001]
* [landau-2000]
-/

@[expose] public section

namespace Wurmbrand2014

open Ogihara1996 (Morpheme readings lf)

/-- The three classes of infinitive of Table 3. A future irrealis infinitive, under *decide* or
*expect*, carries *woll*; a propositional attitude infinitive, under *believe* or *claim*, takes the
attitude holder's NOW as its reference time; a tenseless simultaneous infinitive, under *seem*,
*try*, *manage* or *begin*, has no attitude holder and takes the matrix reference time. -/
inductive InfinitivalTenseClass
  | futureIrrealis
  | propositional
  | tenseless
  deriving DecidableEq, Repr

/-! ### Aspect, (46) and (47) -/

/-- The aspect heads of (46) that the account turns on. -/
inductive Asp
  | perfective
  | imperfective
  deriving DecidableEq

section Aspect

variable {T W E : Type*} [LinearOrder T] [Event.TemporalTrace E (NonemptyInterval T)]

/-- The relation (47) of an aspect between the reference time `t` and an event's run time `s`: the
perfective puts the run time properly inside the reference time, the imperfective the reference
time inside the run time. -/
def Asp.rel : Asp → NonemptyInterval T → NonemptyInterval T → Prop
  | .perfective, t, s => s < t
  | .imperfective, t, s => t ≤ s

/-- An aspect maps a predicate of events to the reference times standing in its relation to the run
time of an event of the predicate, (47). -/
def Asp.denote (a : Asp) (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  Aspect.ofRel a.rel P

-- (47a) is Pancheva's non-strict imperfective
theorem denote_imperfective (P : W → E → Prop) :
    Asp.imperfective.denote P = Aspect.UNBOUNDED P := rfl

/-- A reference time admits a verb phrase of aspect `a` when the run time of some eventuality stands
in the aspect's relation to it; a stative projects no aspect and admits every reference time. -/
def Admits : Option Asp → NonemptyInterval T → Prop
  | none, _ => True
  | some a, r => r ∈ a.denote (fun (_ : Unit) (_ : NonemptyInterval T) ↦ True) ()

variable {r : NonemptyInterval T}

-- (47b): no run time lies properly inside an instant
theorem admits_perfective_iff : Admits (some .perfective) r ↔ ¬ r.IsPoint := by
  refine ⟨fun ⟨s, hs, _⟩ hr ↦ ?_, fun hr ↦ ⟨.pure r.fst, ?_, trivial⟩⟩
  · have hs : s < r := hs
    have hr : r.fst = r.snd := hr
    have hle := NonemptyInterval.le_def.1 hs.le
    have h₁ : s.fst = r.fst := le_antisymm (s.fst_le_snd.trans (hle.2.trans hr.ge)) hle.1
    have h₂ : s.snd = r.snd := le_antisymm hle.2 ((hr.symm.trans h₁.symm).le.trans s.fst_le_snd)
    exact hs.ne (NonemptyInterval.ext (Prod.ext h₁ h₂))
  · show NonemptyInterval.pure r.fst < r
    exact lt_of_le_of_ne (NonemptyInterval.le_def.2 ⟨le_rfl, r.fst_le_snd⟩)
      fun h ↦ hr (congrArg (fun x : NonemptyInterval T ↦ x.snd) h)

@[simp] theorem admits_none (r : NonemptyInterval T) : Admits none r := trivial

@[simp] theorem admits_imperfective (r : NonemptyInterval T) : Admits (some .imperfective) r :=
  ⟨r, (le_rfl : r ≤ r), trivial⟩

theorem not_admits_perfective_pure (t : T) : ¬ Admits (some .perfective) (.pure t) :=
  fun h ↦ admits_perfective_iff.1 h rfl

end Aspect

/-! ### The reference time of an infinitive, §4 -/

section ReferenceTime

variable {T : Type*} [LinearOrder T] (matrixR : NonemptyInterval T) (now : T)

/-- The reference time each class assigns the embedded aspect, given the matrix reference time and
the evaluation instant: after *woll*, any interval after the evaluation time; under a propositional
attitude, the holder's NOW; in a tenseless simultaneous infinitive, the matrix reference time. -/
def ReferenceTime : InfinitivalTenseClass → NonemptyInterval T → Prop
  | .futureIrrealis, r => now < r.fst
  | .propositional, r => r = .pure now
  | .tenseless, r => r = matrixR

/-- A verb phrase of aspect `a` is available in an infinitive of class `c` when some reference time
the class assigns, among the reference times `D` its adverbials allow, admits it. -/
def Available (c : InfinitivalTenseClass) (a : Option Asp) (D : Set (NonemptyInterval T)) :
    Prop :=
  ∃ r ∈ D, ReferenceTime matrixR now c r ∧ Admits a r

variable {matrixR now} {a : Option Asp} {D : Set (NonemptyInterval T)}

theorem available_propositional_iff :
    Available matrixR now .propositional a D ↔ .pure now ∈ D ∧ Admits a (.pure now) := by
  simp [Available, ReferenceTime]

theorem available_tenseless_iff :
    Available matrixR now .tenseless a D ↔ matrixR ∈ D ∧ Admits a matrixR := by
  simp [Available, ReferenceTime]

theorem available_futureIrrealis [NoMaxOrder T] (a : Option Asp) :
    Available matrixR now .futureIrrealis a .univ := by
  obtain ⟨x, hx⟩ := exists_gt now
  obtain ⟨y, hy⟩ := exists_gt x
  have hr : ¬ (⟨(x, y), hy.le⟩ : NonemptyInterval T).IsPoint := hy.ne
  refine ⟨⟨(x, y), hy.le⟩, trivial, hx, ?_⟩
  match a with
  | none => trivial
  | some .perfective => exact admits_perfective_iff.2 hr
  | some .imperfective => exact admits_imperfective _

-- (49), (53b), (68): an adverbial naming an instant excludes the perfective in every class
theorem not_available_perfective (c : InfinitivalTenseClass) (hD : ∀ r ∈ D, r.IsPoint) :
    ¬ Available matrixR now c (some .perfective) D :=
  fun ⟨r, hr, _, h⟩ ↦ admits_perfective_iff.1 h (hD r hr)

/-- Table 3: a bare episodic verb phrase, which is perfective, is possible in a future infinitive,
never in a propositional attitude infinitive, and in a tenseless simultaneous infinitive exactly
when the matrix reference time is extended, as under a past matrix but not a present one. -/
theorem table3 [NoMaxOrder T] :
    Available matrixR now .futureIrrealis (some .perfective) .univ ∧
      ¬ Available matrixR now .propositional (some .perfective) D ∧
      (Available matrixR now .tenseless (some .perfective) .univ ↔ ¬ matrixR.IsPoint) := by
  refine ⟨available_futureIrrealis _, fun h ↦ ?_, ?_⟩
  · exact not_admits_perfective_pure now (available_propositional_iff.1 h).2
  · simp [available_tenseless_iff, admits_perfective_iff]

end ReferenceTime

/-! ### Temporal composition and the sequence of tense, §3 -/

/-- Finite *will*, the present tense over *woll* (21a). -/
def will : List Morpheme := Morpheme.ofForm .english Tense.Form.future

/-- Finite *would*, the past tense over *woll*. -/
def would : List Morpheme := Morpheme.ofForm .english (Tense.Form.simplePast.under .infinitive)

@[simp] theorem will_eq : will = [.s, .woll] := rfl

@[simp] theorem would_eq : would = [.ed, .woll] := rfl

/-- The temporal composition of an infinitive: *woll* without tense in a future infinitive (21b),
nothing in a simultaneous one. -/
def composition : InfinitivalTenseClass → List Morpheme
  | .futureIrrealis => [.woll]
  | .propositional | .tenseless => []

section Locates

variable {T : Type*} [LinearOrder T] {u t e : T}

/-- The times at which a clause with the tense morphemes `ms` places its event, at the local
evaluation time `t` and the utterance time `u`: the absolute present *-s* moves to the utterance
time (21a), and every other morpheme to a time standing in its cell to the time above. -/
def Locates (u : T) : List Morpheme → T → T → Prop
  | [], t, e => e = t
  | .s :: ms, _, e => Locates u ms u e
  | m :: ms, t, e => ∃ t', compare t' t ∈ m.cell ∧ Locates u ms t' e

theorem locates_nil : Locates u [] t e ↔ e = t := .rfl

theorem locates_woll : Locates u [.woll] t e ↔ t < e := by
  simp [Locates, Morpheme.cell, Morpheme.tenses, Tense.denote_future, compare_gt_iff_gt]

theorem locates_will : Locates u will t e ↔ u < e := by
  simpa [Locates] using locates_woll (u := u) (t := u) (e := e)

theorem locates_null_woll : Locates u [.null, .woll] t e ↔ t < e := by
  simp [Locates, Morpheme.cell, Morpheme.tenses, Tense.denote_present, Tense.denote_future,
    compare_gt_iff_gt]

end Locates

/-- The past of *would* deletes under the SOT rule, as *would* requires (29): below the morphemes
`above`, outermost first, its forms at LF include the null tense. -/
def WouldLicensed (above : List Morpheme) : Prop :=
  Morpheme.null ∈ ((lf none (above ++ would)).drop above.length).head?.getD ∅

instance : DecidablePred WouldLicensed := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))

/-- A clause with the tense morphemes `ms` below `above` is licensed unless it is a *would* whose
past cannot delete. -/
def Licensed (above ms : List Morpheme) : Prop := ms = would → WouldLicensed above

instance (above ms : List Morpheme) : Decidable (Licensed above ms) :=
  inferInstanceAs (Decidable (_ → _))

/-- An infinitive is no silent *would*, (29) against (30): under *will* a future infinitive is fine
and a *would* is not, since the local tense feature of *would*'s past is then the present of
*will*, and the past cannot delete as *would* requires. -/
theorem not_silent_would : Licensed will (composition .futureIrrealis) ∧ ¬ Licensed will would := by
  decide

/-! ### The rows -/

section Rows

open Examples

/-- The utterance time, the instant `0`. -/
def present : NonemptyInterval ℤ := .pure 0

/-- Yesterday, an extended interval before the utterance time. -/
def yesterday : NonemptyInterval ℤ := ⟨(-2, -1), by decide⟩

/-- The aspect rows: with the classes the paper gives their verbs, a perfective infinitive is
fine after *woll* and under a past *seem*, *try* or *begin*, and out under a propositional
attitude, a present *seem* or *try*, or an adverbial naming an instant, where the progressive
and statives are fine; finite clauses pattern alike (45), (49). -/
theorem aspect_rows :
    -- (1a), (2a), (53a), (61a): *decide*, *expect* to VP
    (Available present 0 .futureIrrealis (some .perfective) .univ ↔
        ex_1.judgment = .acceptable) ∧
      (Available present 0 .futureIrrealis (some .perfective) .univ ↔
        ex_3.judgment = .acceptable) ∧
      (Available present 0 .futureIrrealis (some .perfective) .univ ↔
        ex_29.judgment = .acceptable) ∧
      (Available present 0 .futureIrrealis (some .perfective) .univ ↔
        ex_43.judgment = .acceptable) ∧
      -- (53b): *expect to work at 5 p.m. tomorrow*
      (Available present 0 .futureIrrealis (some .perfective) {.pure 1} ↔
        ex_30.judgment = .acceptable) ∧
      -- (2b), (3b), (55a), (55b), (56b): *believe*, *claim* to VP
      (Available yesterday (-1) .propositional (some .perfective) .univ ↔
        ex_4.judgment = .acceptable) ∧
      (Available yesterday (-1) .propositional (some .perfective) .univ ↔
        ex_6.judgment = .acceptable) ∧
      (Available present 0 .propositional (some .perfective) .univ ↔
        ex_31.judgment = .acceptable) ∧
      (Available yesterday (-1) .propositional (some .perfective) .univ ↔
        ex_32.judgment = .acceptable) ∧
      (Available yesterday (-1) .propositional (some .perfective) .univ ↔
        ex_35.judgment = .acceptable) ∧
      -- (1b), (3a), (55c): statives under *believe* and *claim*
      (Available present 0 .propositional none .univ ↔ ex_2.judgment = .acceptable) ∧
      (Available yesterday (-1) .propositional none .univ ↔ ex_5.judgment = .acceptable) ∧
      (Available present 0 .propositional none .univ ↔ ex_33.judgment = .acceptable) ∧
      -- (55e), (56e), (61b), (70a): progressives under a propositional attitude
      (Available yesterday (-1) .propositional (some .imperfective) .univ ↔
        ex_34.judgment = .acceptable) ∧
      (Available yesterday (-1) .propositional (some .imperfective) .univ ↔
        ex_36.judgment = .acceptable) ∧
      (Available present 0 .propositional (some .imperfective) .univ ↔
        ex_44.judgment = .acceptable) ∧
      (Available yesterday (-1) .propositional (some .imperfective) .univ ↔
        ex_52.judgment = .acceptable) ∧
      -- (70b), (70d): *seem* with an overt or understood attitude holder
      (Available yesterday (-1) .propositional (some .perfective) .univ ↔
        ex_53.judgment = .acceptable) ∧
      (Available yesterday (-1) .propositional (some .perfective) .univ ↔
        ex_54.judgment = .acceptable) ∧
      -- (57a): a present *seem*, read either way
      (Available present 0 .tenseless (some .perfective) .univ ∨
          Available present 0 .propositional (some .perfective) .univ ↔
        ex_37.judgment = .acceptable) ∧
      -- (57b), (57c), (67c), (67d), (68a), (69a), (69b): *seem*, *try* without an attitude holder
      (Available present 0 .tenseless (some .imperfective) .univ ↔
        ex_38.judgment = .acceptable) ∧
      (Available yesterday (-1) .tenseless (some .perfective) .univ ↔
        ex_39.judgment = .acceptable) ∧
      (Available present 0 .tenseless (some .perfective) .univ ↔
        ex_47.judgment = .acceptable) ∧
      (Available yesterday (-1) .tenseless (some .perfective) .univ ↔
        ex_48.judgment = .acceptable) ∧
      (Available (.pure (-2 : ℤ)) (-2) .tenseless (some .perfective) .univ ↔
        ex_49.judgment = .acceptable) ∧
      (Available yesterday (-1) .tenseless (some .perfective) .univ ↔
        ex_50.judgment = .acceptable) ∧
      (Available present 0 .tenseless (some .perfective) .univ ↔
        ex_51.judgment = .acceptable) ∧
      -- (45a), (45b), (45c), (49a): finite present, past, future, and a past at an instant
      (Admits (some .perfective) (.pure (0 : ℤ)) ↔ ex_23.judgment = .acceptable) ∧
      (Admits (some .perfective) yesterday ↔ ex_24.judgment = .acceptable) ∧
      (Admits (some .perfective) (⟨(1, 2), by decide⟩ : NonemptyInterval ℤ) ↔
        ex_25.judgment = .acceptable) ∧
      (Admits (some .perfective) (.pure (-2 : ℤ)) ↔ ex_26.judgment = .acceptable) := by
  have hf : Available present 0 .futureIrrealis (some .perfective) .univ :=
    available_futureIrrealis _
  have hf' : ¬ Available present 0 .futureIrrealis (some .perfective) {.pure 1} :=
    not_available_perfective _ fun _ h ↦ h ▸ rfl
  simp only [hf, hf', available_propositional_iff, available_tenseless_iff,
    admits_perfective_iff, admits_imperfective, admits_none, Set.mem_univ, true_and,
    NonemptyInterval.IsPoint]
  and_intros <;> decide

/-- The orientation rows: a future infinitive places its event after the matrix event, even before
the utterance time, where *will* places it after the utterance time and a simultaneous infinitive
at the matrix event's time; *would*, its past deleted, is relative like the infinitive. -/
theorem orientation_rows :
    -- (6a), (9b), (12a): *decided*, *is expected* to VP
    (Locates 0 (composition .futureIrrealis) (-1 : ℤ) 1 ↔ ex_7.judgment = .acceptable) ∧
      (Locates 0 (composition .futureIrrealis) (0 : ℤ) 1 ↔ ex_11.judgment = .acceptable) ∧
      (Locates 0 (composition .futureIrrealis) (-7 : ℤ) (-1) ↔ ex_12.judgment = .acceptable) ∧
      -- (12b): *decided … that he will go … yesterday*
      (Locates 0 will (-7 : ℤ) (-1) ↔ ex_13.judgment = .acceptable) ∧
      -- (22a): *decided … that she would go … yesterday*, with the past of *would* deleted
      (Locates 0 [.null, .woll] (-7 : ℤ) (-1) ↔ ex_16.judgment = .acceptable) ∧
      -- (6b), (6d), (66a), (66b): *tried*, *claimed*, *managed*, *began* to VP tomorrow
      (Locates 0 (composition .tenseless) (-1 : ℤ) 1 ↔ ex_8.judgment = .acceptable) ∧
      (Locates 0 (composition .propositional) (-1 : ℤ) 1 ↔ ex_9.judgment = .acceptable) ∧
      (Locates 0 (composition .tenseless) (-1 : ℤ) 1 ↔ ex_45.judgment = .acceptable) ∧
      (Locates 0 (composition .tenseless) (-1 : ℤ) 1 ↔ ex_46.judgment = .acceptable) := by
  simp only [composition, locates_woll, locates_will, locates_null_woll, locates_nil]
  decide

-- (14), (28b), (29a): a higher past lets the past of *would* delete, and *will* does not
theorem would_rows :
    (Licensed will (composition .futureIrrealis) ↔ ex_14.judgment = .acceptable) ∧
      (Licensed will would ↔ ex_15.judgment = .acceptable) ∧
      (Licensed [.ed] would ↔ ex_20.judgment = .acceptable) ∧
      (Licensed will would ↔ ex_21.judgment = .acceptable) := by
  decide

end Rows

/-! ### Recognition by witness

A planar syntactic object over a study lexicon pronounces each sequence-of-tense row's
sentence (`Minimalist.SpellsOut`), and its tense spine is the stack the reader reconstructs, so
the sequence-of-tense verdicts run on derived structure. The witnesses are right-branching
linearizations, each embedded clause a constituent; fuller argument structure is the derivation
step's work. Items take their forms from the English fragment where it declares or realizes
them; the rows' remaining words, names, pronouns and adverbs among them, enter the study lexicon
directly, the adverbs at the adpositional category for want of a closer one. -/

section Witness

open Minimalist Examples

/-- *John*. -/
def liJohn : LexicalItem.Token := ⟨.of .D [] "John", 0⟩

/-- *promised*, the matrix past, `promise` realized at its past cell. -/
def liPromised : LexicalItem.Token := ⟨.of .V [] (English.Verbs.promise.realize .past), 1⟩

/-- *promise*, the base under *will*. -/
def liPromise : LexicalItem.Token := ⟨.of .V [] (English.Verbs.promise.realize .base), 2⟩

/-- *will*, the auxiliary entry. -/
def liWill : LexicalItem.Token := ⟨.of .Mod [] English.Auxiliaries.will.form, 3⟩

/-- *would*, the auxiliary entry. -/
def liWould : LexicalItem.Token := ⟨.of .Mod [] English.Auxiliaries.would.form, 4⟩

/-- The infinitival marker, `toInf`. -/
def liTo : LexicalItem.Token := ⟨.of .T [] English.Auxiliaries.toInf.form, 5⟩

/-- *tell* at its base cell. -/
def liTell : LexicalItem.Token := ⟨.of .V [] (English.Verbs.tell.realize .base), 6⟩

/-- *that*. -/
def liThat : LexicalItem.Token := ⟨.of .C [] "that", 7⟩

/-- The lower *that*, a second token of the same item. -/
def liThat' : LexicalItem.Token := ⟨liThat.item, 8⟩

/-- *were*, the embedded past. -/
def liWere : LexicalItem.Token := ⟨.of .T [] "were", 9⟩

/-- *me*. -/
def liMe : LexicalItem.Token := ⟨.of .D [] "me", 10⟩
/-- *he*. -/
def liHe : LexicalItem.Token := ⟨.of .D [] "he", 11⟩
/-- *his*. -/
def liHis : LexicalItem.Token := ⟨.of .D [] "his", 12⟩
/-- *mother*. -/
def liMother : LexicalItem.Token := ⟨.of .N [] "mother", 13⟩
/-- *they*. -/
def liThey : LexicalItem.Token := ⟨.of .D [] "they", 14⟩
/-- *having*. -/
def liHaving : LexicalItem.Token := ⟨.of .V [] "having", 15⟩
/-- *their*. -/
def liTheir : LexicalItem.Token := ⟨.of .D [] "their", 16⟩
/-- *last*. -/
def liLast : LexicalItem.Token := ⟨.of .A [] "last", 17⟩
/-- *meal*. -/
def liMeal : LexicalItem.Token := ⟨.of .N [] "meal", 18⟩
/-- *together*. -/
def liTogether : LexicalItem.Token := ⟨.of .P [] "together", 19⟩
/-- *yesterday*. -/
def liYesterday : LexicalItem.Token := ⟨.of .P [] "yesterday", 20⟩
/-- *tomorrow*. -/
def liTomorrow : LexicalItem.Token := ⟨.of .P [] "tomorrow", 21⟩
/-- *tonight*. -/
def liTonight : LexicalItem.Token := ⟨.of .P [] "tonight", 22⟩
/-- *when*. -/
def liWhen : LexicalItem.Token := ⟨.of .C [] "when", 23⟩

/-- The study lexicon of the sequence-of-tense sentences, the witness tokens' items. -/
def lexicon : List LexicalItem :=
  ([liJohn, liPromised, liPromise, liWill, liWould, liTo, liTell, liThat, liWere, liMe, liHe,
    liHis, liMother, liThey, liHaving, liTheir, liLast, liMeal, liTogether, liYesterday,
    liTomorrow, liTonight, liWhen] : List LexicalItem.Token).map (·.item)

/-- The deepest clause the rows share, *they were having their last meal together*. -/
def wMeal : PlanarSyntacticObject :=
  liThey * (liWere * (liHaving * (liTheir * (liLast * (liMeal * liTogether)))))

/-- *tell his mother tomorrow* with the complement `k`. -/
def wTell (k : PlanarSyntacticObject) : PlanarSyntacticObject :=
  liTell * (liHis * (liMother * (liTomorrow * k)))

/-- (24a): *John promised me yesterday that he will tell … that they were … (when …)*. -/
def w24a : PlanarSyntacticObject :=
  liJohn * (liPromised * (liMe * (liYesterday * (liThat * (liHe * (liWill *
    wTell (liThat' * (wMeal * liWhen))))))))

/-- (25a): the infinitival variant of (24a). -/
def w25a : PlanarSyntacticObject :=
  liJohn * (liPromised * (liMe * (liYesterday * (liTo * wTell (liThat * wMeal)))))

/-- (27a): the *would* variant of (24a). -/
def w27a : PlanarSyntacticObject :=
  liJohn * (liPromised * (liMe * (liYesterday * (liThat * (liHe * (liWould *
    wTell (liThat' * wMeal)))))))

/-- (29a): *John will promise me tonight that he would tell … that …*, the deepest clause
elided in the text. -/
def w29a : PlanarSyntacticObject :=
  liJohn * (liWill * (liPromise * (liMe * (liTonight * (liThat * (liHe * (liWould *
    wTell ↑liThat')))))))

/-- (30a): the infinitival variant of (29a). -/
def w30a : PlanarSyntacticObject :=
  liJohn * (liWill * (liPromise * (liMe * (liTonight * (liTo *
    wTell (liThat * (wMeal * liWhen)))))))

/-- The tense morphemes a token contributes to its clause: the past *-ed*, *will*, *would*, and
*woll* for the infinitival marker of a future infinitive. -/
def tenseOf (tok : LexicalItem.Token) : Option (List Morpheme) :=
  if tok = liPromised ∨ tok = liWere then some [.ed]
  else if tok = liWill then some will
  else if tok = liWould then some would
  else if tok = liTo then some (composition .futureIrrealis)
  else none

/-- The chain of a witness: the tense morphemes of its clauses, outermost first, in pronounced
order. -/
def chainOf (t : PlanarSyntacticObject) : List (List Morpheme) :=
  (Minimalist.pfYield t).filterMap tenseOf

/-- The five sequence-of-tense rows with their witnesses. -/
def witnessRows : List (Datum × PlanarSyntacticObject) :=
  [(ex_17, w24a), (ex_18, w25a), (ex_19, w27a), (ex_21, w29a), (ex_22, w30a)]

theorem witnesses_spell : ∀ p ∈ witnessRows,
    Minimalist.SpellsOut p.2 lexicon (Minimalist.pfPhon p.2) ∧
      (Minimalist.pfPhon p.2).flatMap (Gloss.tokens ·) = Gloss.tokens p.1.primaryText := by
  decide +kernel

/-- The sequence-of-tense rows (24), (25), (27) and (30), on the chains their witnesses pronounce:
a past under a past can be simultaneous through *would* or a future infinitive, which has no
tense to intervene, but not through *will*, whose present intervenes, and under *will* a past is
only shifted. -/
theorem sot_rows :
    (.eq ∈ readings (chainOf w24a) ↔
        ex_17.readings.lookup "simultaneous (SOT)" = some .acceptable) ∧
      (.lt ∈ readings (chainOf w24a) ↔ ex_17.readings.lookup "shifted past" = some .acceptable) ∧
      (.eq ∈ readings (chainOf w25a) ↔
        ex_18.readings.lookup "simultaneous (SOT)" = some .acceptable) ∧
      (.eq ∈ readings (chainOf w27a) ↔
        ex_19.readings.lookup "simultaneous (SOT)" = some .acceptable) ∧
      (.eq ∈ readings (chainOf w30a) ↔
        ex_22.readings.lookup "simultaneous (SOT)" = some .acceptable) ∧
      (.lt ∈ readings (chainOf w30a) ↔
        ex_22.readings.lookup "shifted past" = some .acceptable) := by
  decide +kernel

end Witness

end Wurmbrand2014
