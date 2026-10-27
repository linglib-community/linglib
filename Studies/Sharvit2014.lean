module

public import Linglib.Data.Examples.Sharvit2014
public import Linglib.Semantics.Composition.Assignment
public import Linglib.Core.Order.Interval.Allen
public import Linglib.Semantics.Tense.Quantificational
public import Linglib.Semantics.Tense.RunTimes
public import Studies.Sharvit2003
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Tactic.NormNum.Ineq

/-!
# Sharvit (2014): On the universal principles of tense embedding: The lesson from *before*

Sharvit derives the tenses a language allows in *before*-clauses from the kind of tense it has.
*Before* presupposes, with Beaver and Condoravdi, an earliest time of its clause within the
contextually relevant interval, later than the start of that interval. A tense that quantifies
existentially over times makes the presupposition fail on dense time: the times after some event
have no earliest member, and where the event precedes the interval, the interval itself
qualifies. A pronominal tense, after Partee, has no quantifier and leaves an earliest time,
which its own presupposition places before the speech time. A tense with no meaning of its own,
deleted by the sequence-of-tense rule or null, leaves the earliest time unconstrained. A present
whose evaluation time stays the speech time makes the order of the two events follow from the
tenses alone, the effect noted by Stump. With the sequence-of-tense rule and the shiftability of
the present as parameters, the kind of tense gives the pattern of English, Japanese and Polish,
a table of permissible languages, and three predictions.

## Implementation notes

* A time is a closed interval of a dense linear order of moments, mathlib's `NonemptyInterval`,
  and precedence and overlap are those of `Semantics/Tense/Perspective.lean`.
* *Before* is the extensional one of the main text, and the contextual restrictor of the
  quantificational past is left out, as in the paper's own derivations.
* The Stump effect is the entailment the paper identifies, that the matrix event ends before the
  embedded one does, and not a pragmatic principle that rules the sentence out.
* The simultaneous readings of attitude reports are those of `Studies/Sharvit2003.lean`, and
  the examples are the rows of `Data.Examples.Sharvit2014`.

## TODO

* Modern Greek and the two Spanish varieties need a mood parameter and a language whose past and
  present differ in kind, which the parameters here cannot express.
* The intensional *before* of the appendix, the relative-clause analysis and Geis ambiguities,
  and the behaviour of the present in relative clauses are not formalized.

## References

* [sharvit-2014]
* [sharvit-2003]
* [beaver-condoravdi-2003]
* [partee-1973]
* [prior-1967]
* [stump-1985]
* [ogihara-sharvit-2012]
-/

@[expose] public section

namespace Sharvit2014

open ModalLogic Tense Montague
open scoped Denotes
open Sharvit2003 (Embedded)
open scoped SetRel

variable {M : Type*} [LinearOrder M] {C SP t d : NonemptyInterval M}
  {P q : Set (NonemptyInterval M)} {m : M}

/-! ### The earliest time and *before* -/

/-- `IsEarliest C P m` says that `m` is the leftmost moment of the intervals of `P` within `C`, the
EARLIEST of (23). -/
def IsEarliest (C : NonemptyInterval M) (P : Set (NonemptyInterval M)) (m : M) : Prop :=
  IsLeast (timeTrace (P ∩ Set.Iic C)) m

theorem IsEarliest.fst_le (h : IsEarliest C P m) : C.fst ≤ m :=
  let ⟨_, ⟨_, ht⟩, hm⟩ := h.1
  (NonemptyInterval.le_def.1 ht).1.trans hm.1

theorem IsEarliest.le_of_mem (h : IsEarliest C P m) (ht : t ∈ P) (htC : t ≤ C) {a : M}
    (ha : a ∈ t) : m ≤ a :=
  h.2 ⟨t, ⟨ht, htC⟩, ha⟩

theorem IsEarliest.eq_fst_of_mem (h : IsEarliest C P m) (hC : C ∈ P) : m = C.fst :=
  le_antisymm (h.le_of_mem hC le_rfl ⟨le_rfl, C.fst_le_snd⟩) h.fst_le

theorem isEarliest_fst_of_subset_singleton (hd : d ∈ P) (hP : P ⊆ {d}) (hdC : d ≤ C) :
    IsEarliest C P d.fst :=
  ⟨⟨d, ⟨hd, hdC⟩, le_rfl, d.fst_le_snd⟩, fun _ ⟨_, ⟨ht, _⟩, ha⟩ ↦ hP ht ▸ ha.1⟩

/-- *Before* (24) presupposes that its clause has an earliest moment within the contextually
relevant interval `C`, later than the start of `C`. -/
def BeforeDefined (C : NonemptyInterval M) (P : Set (NonemptyInterval M)) : Prop :=
  ∃ m, IsEarliest C P m ∧ C.fst < m


/-- On dense time, the earliest moment of a clause with an existentially quantified tense is the
start of the contextually relevant interval, whatever the cell of the tense. A clause time that
follows a time of the predicate can be started later, one that overlaps it can be widened to the
whole interval, and one that precedes it can be started at the start of the interval. -/
theorem IsEarliest.eq_fst_of_diamond [DenselyOrdered M] {c : Finset Ordering}
    (h : IsEarliest C {t | ◇[Perspective.toSetRel (Allen.ofPosition c)] (· ∈ q) t} m) :
    m = C.fst := by
  refine h.fst_le.eq_of_not_lt' fun hlt ↦ ?_
  obtain ⟨t, ⟨⟨r, hr, hq⟩, htC⟩, hm⟩ := h.1
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 htC
  rw [Perspective.mem_toSetRel, Perspective.presup_ofPosition] at hr
  rcases hpos : r.position t with _ | _ | _
  · have hrt : r.snd < t.fst := NonemptyInterval.position_eq_lt.1 hpos
    obtain ⟨a, ha, ham⟩ := exists_between (max_lt (hrt.trans_le hm.1) hlt)
    have hra : r.position (.pure a) = .lt :=
      NonemptyInterval.position_eq_lt.2 ((le_max_left _ _).trans_lt ha)
    exact absurd (h.le_of_mem (t := .pure a) ⟨r, by rwa [Perspective.mem_toSetRel,
      Perspective.presup_ofPosition, hra, ← hpos], hq⟩ (NonemptyInterval.le_def.2
        ⟨(le_max_right _ _).trans ha.le, ham.le.trans (hm.2.trans h₂)⟩)
      (NonemptyInterval.mem_pure_self a)) ham.not_ge
  · have hrC : r.position C = .eq := NonemptyInterval.position_eq_eq.2
      ((NonemptyInterval.overlaps_comm _ _).1 (((NonemptyInterval.overlaps_comm _ _).1
        (NonemptyInterval.position_eq_eq.1 hpos)).mono_left htC))
    exact hlt.ne' (h.eq_fst_of_mem ⟨r, by
      rwa [Perspective.mem_toSetRel, Perspective.presup_ofPosition, hrC, ← hpos], hq⟩)
  · have hra : r.position (.pure C.fst) = .gt := NonemptyInterval.position_eq_gt.2
      ((h₁.trans t.fst_le_snd).trans_lt (NonemptyInterval.position_eq_gt.1 hpos))
    exact hlt.not_ge (h.le_of_mem (t := .pure C.fst) ⟨r, by rwa [Perspective.mem_toSetRel,
      Perspective.presup_ofPosition, hra, ← hpos], hq⟩
      (NonemptyInterval.le_def.2 ⟨le_rfl, C.fst_le_snd⟩) (NonemptyInterval.mem_pure_self _))

-- (27)
theorem not_beforeDefined_diamond [DenselyOrdered M] {c : Finset Ordering} :
    ¬ BeforeDefined C {t | ◇[Perspective.toSetRel (Allen.ofPosition c)] (· ∈ q) t} :=
  fun ⟨_, h, hlt⟩ ↦ hlt.ne' h.eq_fst_of_diamond

/-! ### Tensed clauses under *before* -/

/-- The cell of an embedded tense. -/
def cell : Embedded → Finset Ordering
  | .past => ⟦Tense.past⟧
  | .present => ⟦Tense.present⟧

@[simp] theorem presup_cell_past {π t : NonemptyInterval M} :
    Perspective.Presup (Allen.ofPosition (cell .past)) π t ↔ t.Precedes π := by
  simp [cell, Tense.denote_past]

@[simp] theorem presup_cell_present {π t : NonemptyInterval M} :
    Perspective.Presup (Allen.ofPosition (cell .present)) π t ↔ t.Overlaps π := by
  simp [cell, Tense.denote_present]

/-- The readings of a tensed clause that is the complement of *before*. -/
inductive Reading
  /-- A pronominal tense whose referential index *before* binds and whose evaluation index is
  free, hence the speech time, as in (35) and (37). -/
  | pronominal (τ : Embedded)
  /-- A quantificational tense (34), or a pronominal one whose evaluation index *before* binds
  and whose referential index is existentially closed (42). -/
  | existential (τ : Embedded)
  /-- A tense with no meaning of its own, whether deleted by the sequence-of-tense rule (56),
  a null present (36), or a present with both indices bound by *before* (44). -/
  | null
  deriving DecidableEq, Fintype

/-- The times a clause holds at on a reading, with `q` the times of its predicate and `SP` the
speech time. -/
def Reading.denote (SP : NonemptyInterval M) (q : Set (NonemptyInterval M)) :
    Reading → Set (NonemptyInterval M)
  | .pronominal τ => {t | Perspective.Presup (Allen.ofPosition (cell τ)) SP t ∧ t ∈ q}
  | .existential τ => {t | ◇[Perspective.toSetRel (Allen.ofPosition (cell τ))] (· ∈ q) t}
  | .null => q

/-- A clause whose verb takes the pronominal tense `τ` with evaluation index `j` and referential
index `k`, as in (30a), says that the time of `k` stands to the time of `j` as the tense requires
and that the predicate holds at it. -/
def clause (τ : Embedded) (j k : ℕ) (q : Set (NonemptyInterval M)) :
    Assignment (NonemptyInterval M) → Prop :=
  fun g ↦ Perspective.Presup (Allen.ofPosition (cell τ)) (g j) (g k) ∧ g k ∈ q

variable {τ : Embedded} {j k : ℕ} {g : Assignment (NonemptyInterval M)}

theorem lambdaAbsG_clause (hjk : j ≠ k) :
    {t | lambdaAbsG k (clause τ j k q) g t} = (Reading.pronominal τ).denote (g j) q := by
  ext t
  simp [clause, Reading.denote, Function.update_of_ne hjk]

theorem lambdaAbsG_exists_clause (hjk : j ≠ k) :
    {t | lambdaAbsG j (fun g ↦ ∃ t', lambdaAbsG k (clause τ j k q) g t') g t} =
      (Reading.existential τ).denote SP q := by
  ext t
  simp [clause, Reading.denote, Diamond, Function.update_of_ne hjk]

theorem lambdaAbsG_clause_self :
    {t | lambdaAbsG k (clause .present k k q) g t} = Reading.null.denote SP q := by
  ext t
  simp [clause, Reading.denote, cell, Tense.denote_present]

namespace Reading

/-- A reading fails when on dense time its clause never satisfies the presupposition of
*before*, the paper's inherent presupposition failure. -/
def Fails (r : Reading) : Prop :=
  ∀ (M : Type) [LinearOrder M] [DenselyOrdered M] (C SP : NonemptyInterval M)
    (q : Set (NonemptyInterval M)), ¬ BeforeDefined C (r.denote SP q)

/-- A reading has the Stump effect when every past time ends before each time of the clause
does, so that the order of the two events follows from the tenses alone. -/
def StumpEffect (r : Reading) : Prop :=
  ∀ (M : Type) [LinearOrder M] (SP t d : NonemptyInterval M) (q : Set (NonemptyInterval M)),
    t.Precedes SP → d ∈ r.denote SP q → t.snd < d.snd

/-- A reading has no p-shiftability when the earliest time of the clause precedes the speech
time. -/
def NoPShiftability (r : Reading) : Prop :=
  ∀ (M : Type) [LinearOrder M] (C SP : NonemptyInterval M) (q : Set (NonemptyInterval M)) (m : M),
    IsEarliest C (r.denote SP q) m → m < SP.fst

/-- The existential readings are the ones that fail. -/
theorem fails_iff {r : Reading} : r.Fails ↔ ∃ τ, r = .existential τ := by
  refine ⟨fun h ↦ ?_, fun ⟨τ, hτ⟩ M _ _ C SP q ↦ hτ ▸ not_beforeDefined_diamond⟩
  have key : ∀ (SP : NonemptyInterval ℚ) (r : Reading),
      NonemptyInterval.pure 5 ∈ r.denote SP {.pure 5} → r.denote SP {.pure 5} ⊆ {.pure 5} →
        ¬ r.Fails := fun SP r h₁ h₂ h ↦
    h ℚ ⟨(0, 10), by norm_num⟩ SP {.pure 5} ⟨5, isEarliest_fst_of_subset_singleton h₁ h₂
      (NonemptyInterval.le_def.2 ⟨by norm_num, by norm_num⟩), by norm_num⟩
  rcases r with (_ | _) | τ | _
  · exact absurd h (key (.pure 20) _ ⟨presup_cell_past.2 (by
      show (5 : ℚ) < 20; norm_num), rfl⟩ fun _ h ↦ h.2)
  · exact absurd h (key (.pure 5) _ ⟨presup_cell_present.2
      (NonemptyInterval.overlaps_refl _), rfl⟩ fun _ h ↦ h.2)
  · exact ⟨τ, rfl⟩
  · exact absurd h (key (.pure 0) _ rfl subset_rfl)

/-- The pronominal present is the reading with the Stump effect. -/
theorem stumpEffect_iff {r : Reading} : r.StumpEffect ↔ r = .pronominal .present := by
  refine ⟨fun h ↦ ?_, fun hr M _ SP t d q ht hd ↦ ?_⟩
  · have key : ∀ r : Reading, (NonemptyInterval.pure 1 : NonemptyInterval ℤ) ∈
        r.denote (.pure 10) {.pure 0, .pure 1} → ¬ r.StumpEffect := fun r hd h ↦
      absurd (h ℤ (.pure 10) (.pure 5) (.pure 1) _ (by decide) hd) (by decide)
    rcases r with (_ | _) | (_ | _) | _
    · exact absurd h (key _ ⟨presup_cell_past.2 (by decide), by simp⟩)
    · rfl
    · exact absurd h (key _ ⟨.pure 0, presup_cell_past.2 (by decide), by simp⟩)
    · exact absurd h (key _ ⟨.pure 1, presup_cell_present.2 (by decide), by simp⟩)
    · exact absurd h (key _ (by simp [denote]))
  · subst hr
    exact ht.trans_le (presup_cell_present.1 hd.1).2

-- (35)
theorem noPShiftability_pronominal_past : (pronominal .past).NoPShiftability :=
  fun _ _ _ _ _ _ h ↦
    let ⟨_, ⟨ht, _⟩, hm⟩ := h.1
    hm.2.trans_lt (presup_cell_past.1 ht.1)

-- (36)
theorem not_noPShiftability_null : ¬ null.NoPShiftability := fun h ↦
  absurd (h ℤ ⟨(0, 10), by decide⟩ (.pure 2) {.pure 5} 5 (isEarliest_fst_of_subset_singleton
    (d := .pure 5) (Set.mem_singleton _) subset_rfl (by decide))) (by decide)

/-- A reading is felicitous when it neither fails nor has the Stump effect. -/
def Felicitous (r : Reading) : Prop := ¬ r.Fails ∧ ¬ r.StumpEffect

theorem felicitous_iff {r : Reading} : r.Felicitous ↔ r = .pronominal .past ∨ r = .null := by
  rw [Felicitous, fails_iff, stumpEffect_iff]
  rcases r with (_ | _) | τ | _ <;> simp

end Reading

/-! ### Languages -/

/-- The shiftability of a present tense (71) says whether its evaluation index must be free, may be
bound though not by the binder of its referential index, or may be bound freely. -/
inductive Shiftability
  | non | semi | full
  deriving DecidableEq, Fintype, Repr

/-- A language's tense parameters say whether it has the sequence-of-tense rule, how shiftable its
present is, and whether it has pronominal and quantificational tenses. -/
structure Language where
  /-- The language has the sequence-of-tense rule. -/
  sot : Bool
  /-- The shiftability of the present. -/
  present : Shiftability
  /-- The language has pronominal tenses. -/
  pronominal : Bool
  /-- The language has quantificational tenses. -/
  quantificational : Bool
  deriving DecidableEq, Fintype, Repr

namespace Language

variable (L : Language) (τ : Embedded)

/-- A language gives a tense in a *before*-clause its existential reading when the tense is a
quantificational past (34), a pronominal past, whose evaluation index may always be bound (42b),
or a pronominal present whose evaluation index may be bound (69b). -/
def HasExistential : Embedded → Prop
  | .past => L.pronominal ∨ L.quantificational
  | .present => L.pronominal ∧ L.present ≠ .non

/-- A language gives a tense in a *before*-clause no meaning of its own when the tense is a past
that a quantificational matrix past raises above and deletes (56), since a pronominal matrix
past does not raise (60), or a fully shiftable present, null if quantificational (36) and with
both indices bound by *before* if pronominal (44). -/
def HasNull : Embedded → Prop
  | .past => L.quantificational ∧ L.sot
  | .present => (L.pronominal ∨ L.quantificational) ∧ L.present = .full

instance : DecidablePred L.HasNull
  | .past => inferInstanceAs (Decidable (_ ∧ _))
  | .present => inferInstanceAs (Decidable (_ ∧ _))

/-- The readings a language's grammar gives the tense `τ` of a *before*-clause under a past. -/
def Available : Reading → Prop
  | .pronominal τ' => τ' = τ ∧ L.pronominal
  | .existential τ' => τ' = τ ∧ L.HasExistential τ
  | .null => L.HasNull τ

/-- The tense `τ` is well-formed in a *before*-clause under a past when it has a felicitous
reading there. -/
def WellFormed : Prop := ∃ r, L.Available τ r ∧ r.Felicitous

/-- A *before*-clause in the tense `τ` is p-shiftable when a felicitous reading lets its time
follow the speech time. -/
def PShiftable : Prop := ∃ r, L.Available τ r ∧ r.Felicitous ∧ ¬ r.NoPShiftability

/-- A *before*-clause in the tense `τ` has no p-shiftability when it is well-formed and its time
precedes the speech time on every felicitous reading. -/
def NoPShiftability : Prop :=
  L.WellFormed τ ∧ ∀ r, L.Available τ r → r.Felicitous → r.NoPShiftability

variable {L τ}

theorem wellFormed_iff : L.WellFormed τ ↔ τ = .past ∧ L.pronominal ∨ L.HasNull τ := by
  simp only [WellFormed, Reading.felicitous_iff]
  constructor
  · rintro ⟨r, ha, rfl | rfl⟩
    exacts [.inl ⟨ha.1.symm, ha.2⟩, .inr ha]
  · rintro (⟨rfl, h⟩ | h)
    exacts [⟨.pronominal .past, ⟨rfl, h⟩, .inl rfl⟩, ⟨.null, h, .inr rfl⟩]

theorem pShiftable_iff : L.PShiftable τ ↔ L.HasNull τ := by
  simp only [PShiftable, Reading.felicitous_iff]
  constructor
  · rintro ⟨r, ha, rfl | rfl, hn⟩
    exacts [absurd Reading.noPShiftability_pronominal_past hn, ha]
  · exact fun h ↦ ⟨.null, h, .inr rfl, Reading.not_noPShiftability_null⟩

instance : Decidable (L.WellFormed τ) := decidable_of_iff _ wellFormed_iff.symm

instance : Decidable (L.PShiftable τ) := decidable_of_iff _ pShiftable_iff.symm

theorem noPShiftability_iff : L.NoPShiftability τ ↔ L.WellFormed τ ∧ ¬ L.PShiftable τ :=
  and_congr_right fun _ ↦
    ⟨fun h ⟨r, ha, hf, hn⟩ ↦ hn (h r ha hf), fun h r ha hf ↦ by_contra fun hn ↦ h ⟨r, ha, hf, hn⟩⟩

variable (L)

/-- The language as a type of Sharvit's earlier typology, which has the sequence-of-tense rule
and whether the present may be bound. -/
def toSharvit2003 : Sharvit2003.Language :=
  ⟨L.sot, if L.present = .non then .matrixIndexical else .bindable⟩

/-- The tense `τ` under a past attitude verb has a simultaneous reading, a past where the
sequence-of-tense rule deletes it and a present where its evaluation index may be bound. -/
def Simultaneous (τ : Embedded) : Prop := Sharvit2003.NonpastAvailable L.toSharvit2003 τ

instance (τ : Embedded) : Decidable (L.Simultaneous τ) :=
  inferInstanceAs (Decidable (Sharvit2003.NonpastAvailable _ _))

variable {L}

theorem simultaneous_past_iff : L.Simultaneous .past ↔ L.sot :=
  eq_mem_pastUnderPast_iff

end Language

/-! ### English, Japanese and Polish -/

/-- English has the sequence-of-tense rule, a present that cannot be bound, and pronominal
tenses. -/
def english : Language := ⟨true, .non, true, false⟩

/-- Japanese has no sequence-of-tense rule, a fully shiftable present, and quantificational
tenses. -/
def japanese : Language := ⟨false, .full, false, true⟩

/-- Polish has no sequence-of-tense rule, a semi-shiftable present, and pronominal tenses. -/
def polish : Language := ⟨false, .semi, true, false⟩

theorem toSharvit2003_eq : english.toSharvit2003 = Sharvit2003.english ∧
    japanese.toSharvit2003 = Sharvit2003.hebrew ∧ polish.toSharvit2003 = Sharvit2003.hebrew :=
  ⟨rfl, rfl, rfl⟩

-- (34)
theorem japanese_past_fails {r : Reading} (h : japanese.Available .past r) : r.Fails := by
  rcases r with τ | τ | _
  · exact absurd h.2 (by decide)
  · exact Reading.fails_iff.2 ⟨τ, rfl⟩
  · exact absurd h.2 (by decide)

-- (37)
theorem english_present_stumpEffect {r : Reading} (h : english.Available .present r) :
    r.StumpEffect := by
  rcases r with τ | τ | _
  · obtain rfl := h.1
    exact Reading.stumpEffect_iff.2 rfl
  · exact absurd h.2.2 (by decide)
  · exact absurd h.2 (by decide)

-- (69b)
theorem polish_present_fails_or_stumpEffect {r : Reading} (h : polish.Available .present r) :
    r.Fails ∨ r.StumpEffect := by
  rcases r with τ | τ | _
  · obtain rfl := h.1
    exact .inr (Reading.stumpEffect_iff.2 rfl)
  · exact .inl (Reading.fails_iff.2 ⟨τ, rfl⟩)
  · exact absurd h.2 (by decide)

/-- The languages of the example rows. -/
def languages : List (String × Language) :=
  [("stan1293", english), ("nucl1643", japanese), ("poli1260", polish)]

/-- The embedded tenses of the example rows. -/
def tenses : List (String × Embedded) := [("past", .past), ("present", .present)]

/-- A tense in a *before*-clause under a past is acceptable exactly where the language's
parameters make it well-formed. -/
theorem judgment_iff :
    ∀ e ∈ Examples.all, e.language ≠ "mode1248" → e.feature? "construction" = some "before" →
      e.feature? "clauseTime" ≠ some "after speech" →
      ∃ L ∈ languages.lookup e.language, ∃ τ ∈ e.parse? "embedded" tenses,
        (e.judgment = .acceptable ↔ L.WellFormed τ) := by
  decide

theorem clauseTime_iff :
    ∀ e ∈ Examples.all, e.feature? "clauseTime" = some "after speech" →
      ∃ L ∈ languages.lookup e.language, ∃ τ ∈ e.parse? "embedded" tenses,
        (e.judgment = .acceptable ↔ L.PShiftable τ) := by
  decide

/-- A tense under a past attitude verb has a simultaneous reading exactly where the language's
parameters give it one. -/
theorem simultaneous_iff :
    ∀ e ∈ Examples.all, e.language ≠ "mode1248" → e.feature? "construction" = some "attitude" →
      ∃ L ∈ languages.lookup e.language, ∃ τ ∈ e.parse? "embedded" tenses,
        (e.readings.lookup "simultaneous" = some .acceptable ↔ L.Simultaneous τ) := by
  decide

/-! ### Permissible languages -/

namespace Language

variable (L : Language)

/-- A language is permissible when it has tenses of exactly one kind and meets the Embeddability
Principle for attitude reports, having the sequence-of-tense rule or a present that may be
bound. -/
def Permissible : Prop :=
  (L.pronominal ∨ L.quantificational) ∧ ¬ (L.pronominal ∧ L.quantificational) ∧
    Sharvit2003.EmbeddabilityPrinciple L.toSharvit2003

instance : Decidable L.Permissible := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The number of a language's type in the table of language types (98), which lists the
sixteen settings of the sequence-of-tense rule, a shiftable present, pronominal tenses and
quantificational tenses. -/
def row : ℕ :=
  1 + (if L.sot then 0 else 8) + (if L.present = .non then 4 else 0) +
    (if L.pronominal then 0 else 2) + (if L.quantificational then 0 else 1)

theorem permissible_iff : L.Permissible ↔ L.row ∈ ({2, 3, 6, 7, 10, 11} : Finset ℕ) := by
  revert L
  decide

theorem permissible_without_economy_iff :
    (L.pronominal ∨ L.quantificational) ∧ Sharvit2003.EmbeddabilityPrinciple L.toSharvit2003 ↔
      L.row ∈ ({1, 2, 3, 5, 6, 7, 9, 10, 11} : Finset ℕ) := by
  revert L
  decide

variable {L}

theorem wellFormed_past_or_present_iff :
    L.WellFormed .past ∨ L.WellFormed .present ↔
      L.pronominal ∨ L.quantificational ∧ (L.sot ∨ L.present = .full) := by
  revert L
  decide

end Language

theorem row_eq : english.row = 6 ∧ polish.row = 10 ∧ japanese.row = 11 := by decide

theorem semiShiftable_quantificational :
    ({ japanese with present := .semi } : Language).Permissible ∧
      ¬ ({ japanese with present := .semi } : Language).WellFormed .past ∧
      ¬ ({ japanese with present := .semi } : Language).WellFormed .present := by
  decide

/-! ### Predictions -/

variable {L : Language}

/-- A language with a well-formed present in *before*-clauses under a past has p-shiftability
there (99a), since the present is then fully shiftable. -/
theorem pShiftable_present_of_wellFormed (h : L.WellFormed .present) : L.PShiftable .present :=
  Language.pShiftable_iff.2
    ((Language.wellFormed_iff.1 h).resolve_left fun h ↦ Embedded.noConfusion h.1)

/-- A language with p-shiftability in past *before*-clauses under a past has simultaneous
past-under-past readings (99b). -/
theorem simultaneous_past_of_pShiftable (h : L.PShiftable .past) : L.Simultaneous .past :=
  Language.simultaneous_past_iff.2 (Language.pShiftable_iff.1 h).2

/-- A language with a well-formed past in *before*-clauses under a past but no simultaneous
past-under-past reading has no p-shiftability there (99c). -/
theorem noPShiftability_past_of_not_simultaneous (hw : L.WellFormed .past)
    (hs : ¬ L.Simultaneous .past) : L.NoPShiftability .past :=
  Language.noPShiftability_iff.2 ⟨hw, fun h ↦ hs (simultaneous_past_of_pShiftable h)⟩

-- (102)
theorem wellFormed_past_of_simultaneous (ht : L.pronominal ∨ L.quantificational)
    (h : L.Simultaneous .past) : L.WellFormed .past :=
  Language.wellFormed_iff.2 (ht.imp (⟨rfl, ·⟩) (⟨·, Language.simultaneous_past_iff.1 h⟩))

-- (104), (103)
theorem not_exists_modernGreek :
    ¬ ∃ L : Language, (L.pronominal ∨ L.quantificational) ∧
      (Examples.ex_104.readings.lookup "simultaneous" = some .acceptable ↔ L.Simultaneous .past) ∧
      (Examples.ex_103.judgment = .acceptable ↔ L.WellFormed .past) := by
  decide

end Sharvit2014
