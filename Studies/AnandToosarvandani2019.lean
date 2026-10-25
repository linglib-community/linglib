module

public import Linglib.Fragments.English.TemporalDeictic
public import Linglib.Data.Examples.AnandToosarvandani2019

/-!
# Anand and Toosarvandani (2019): Now and then

*now* and *then* are temporal demonstratives indexical to an assessment time `a` rather than to
the utterance time `u`: *now* refers to a time within `a`, *then* to a time disjoint from it,
(12). A demonstrative restricts the reference of its sentence's tense through a silent IN, (13).
*now* needs R-PAST, whose reference lies within an assessment time before the utterance, (17);
*then* needs PAST, whose reference precedes the assessment time, (15). The assessment time is the
utterance time or starts with the most recent eventuality, CATS (31). In initial position a
demonstrative is a contrastive topic whose alternatives are disjoint, (28), so it cannot overlap
a preceding sentence that answers a sister subquestion; with CATS, a *now* sentence cannot
precede the preceding sentence. These give the positional generalization (45).

## Main results

* `AnandToosarvandani2019.not_restricted_now_past`: *now* is incompatible with PAST.
* `AnandToosarvandani2019.not_precedes_of_cats`: under CATS a reference within an assessment time
  before the utterance cannot precede the most recent eventuality, so *now* does not backshift.
* `AnandToosarvandani2019.eq_of_cats_of_presup_then`: final *then* places the assessment time at
  the utterance time (41).
* `AnandToosarvandani2019.admits_iff`: the account derives the positional generalization (45).
* `AnandToosarvandani2019.accepted_iff_admits`: a reading of an example is accepted exactly when
  the account admits it.

## Implementation notes

The contexts enter only through their times; `τ₀` is the time of the preceding sentence, the top
of the eventuality stack, and the account is evaluated on `ℤ`. The examples record the strategy
of inquiry: whether the preceding sentence answers a sister subquestion, and whether an earlier
time is retrievable. A final demonstrative is anaphoric to `τ₀`. The clash of an overlapping state
in (7) and (36b) is the aspectual constraint of Partee's (6), outside the account.

## References

* [anand-toosarvandani-2019]
* [partee-1984]
-/

@[expose] public section

namespace AnandToosarvandani2019

open Tense Tense.Perspective
open scoped Denotes

variable {T : Type*} [LinearOrder T] {a u τ₀ r J : NonemptyInterval T}

/-! ### Tenses and demonstratives (section 3) -/

/-- The past tenses. -/
inductive Past where
  /-- PAST, (15): the reference precedes the assessment time. -/
  | past
  /-- R(EMOTE)-PAST, (17): the reference lies within an assessment time before the utterance. -/
  | remote
  deriving DecidableEq

/-- The cell of a past tense's reference relative to the assessment time. -/
def Past.cell : Past → Finset Allen.Relation
  | .past => Allen.precedes
  | .remote => Allen.le

/-- The temporal demonstratives. -/
inductive Demonstrative where
  | now
  | then
  deriving DecidableEq

/-- The cell of a demonstrative's interval relative to the assessment time: within it for *now*,
(12a), and disjoint from it for *then*, the English entry, (12b). -/
def Demonstrative.cell : Demonstrative → Finset Allen.Relation
  | .now => Allen.le
  | .then => Allen.ofPosition English.TemporalDeictic.then_.cell

theorem presup_then : Presup Demonstrative.then.cell a J ↔ ¬ J.Overlaps a := by
  simp [Demonstrative.cell, English.TemporalDeictic.then_, denote_present]

/-- Only R-PAST is compatible with *now* (p. 24): a reference within the *now*-interval lies
within the assessment time and cannot precede it. -/
theorem not_restricted_now_past : ¬ Restricted Past.past.cell Demonstrative.now.cell a r J :=
  fun ⟨hr, hle, hJ⟩ ↦ NonemptyInterval.precedes_not_overlaps (presup_precedes.1 hr)
    (NonemptyInterval.overlaps_of_le (hle.trans (presup_le.1 hJ)))

/-- *then* is incompatible with R-PAST (p. 31): a reference within the assessment time would make
the *then*-interval containing it overlap the assessment time. -/
theorem not_restricted_then_remote : ¬ Restricted Past.remote.cell Demonstrative.then.cell a r J :=
  fun ⟨hr, hle, hJ⟩ ↦ presup_then.1 hJ
    ((NonemptyInterval.overlaps_of_le (presup_le.1 hr)).mono_left hle)

/-! ### The assessment time (section 4.2) -/

/-- CATS, (31): the assessment time is the utterance time, or a time preceded by exactly the times
that precede the time `τ₀` of the most recent eventuality. -/
def Cats (a u τ₀ : NonemptyInterval T) : Prop :=
  a = u ∨ ∀ t : NonemptyInterval T, t.Precedes a ↔ t.Precedes τ₀

/-- A time is preceded by exactly the times that precede another when the two start together. -/
theorem forall_precedes_iff_iff_fst_eq :
    (∀ t : NonemptyInterval T, t.Precedes a ↔ t.Precedes τ₀) ↔ a.fst = τ₀.fst := by
  refine ⟨fun h ↦ le_antisymm ?_ ?_, fun h t ↦ by rw [NonemptyInterval.Precedes, h]; rfl⟩
  · exact not_lt.1 fun hlt ↦ lt_irrefl τ₀.fst ((h (.pure τ₀.fst)).1 hlt)
  · exact not_lt.1 fun hlt ↦ lt_irrefl a.fst ((h (.pure a.fst)).2 hlt)

/-- No going backwards (29): under CATS a reference within an assessment time that precedes the
utterance time cannot precede the time of the most recent eventuality. -/
theorem not_precedes_of_cats (h : Cats a u τ₀) (hr : r ≤ a) (hau : a.Precedes u) :
    ¬ r.Precedes τ₀ := by
  rcases h with rfl | h
  · exact absurd hau (NonemptyInterval.precedes_irrefl _)
  · exact fun hrτ ↦ NonemptyInterval.precedes_not_overlaps ((h r).2 hrτ)
      (NonemptyInterval.overlaps_of_le hr)

/-- Final *then*, (41): when the *then*-interval is the time of the most recent eventuality, CATS
leaves the utterance time as the only assessment time, which the paper offers as one
possibility. -/
theorem eq_of_cats_of_presup_then (h : Cats a u τ₀) (hJ : Presup Demonstrative.then.cell a τ₀) :
    a = u := by
  refine h.resolve_right fun h' ↦ presup_then.1 hJ ?_
  have hfst := forall_precedes_iff_iff_fst_eq.1 h'
  exact ⟨by rw [← hfst]; exact a.fst_le_snd, by rw [hfst]; exact τ₀.fst_le_snd⟩

/-! ### Position (sections 4 and 6) -/

/-- The position of a demonstrative in its sentence. -/
inductive Position where
  | initial
  | final
  deriving DecidableEq

/-- The positions, relative to the time of the preceding sentence, of the intervals a
sentence-initial demonstrative may pick out: a later time by Narration as Default (33), an earlier
time when the discourse makes one retrievable, and an overlapping time unless the preceding
sentence answers a sister subquestion, whose alternatives are disjoint (28). -/
def initialPositions (sister anterior : Bool) : Finset Ordering :=
  {.gt} ∪ (if anterior then {.lt} else ∅) ∪ (if sister then ∅ else {.eq})

/-- The demonstrative's interval `J`: the time `τ₀` of the preceding sentence in final position,
and a time in one of `initialPositions` relative to it in initial position. -/
def Licensed (sister anterior : Bool) : Position → (J τ₀ : NonemptyInterval T) → Prop
  | .initial, J, τ₀ => J.position τ₀ ∈ initialPositions sister anterior
  | .final, J, τ₀ => J = τ₀

/-- A sentence with demonstrative `d` in position `p` can stand to the preceding sentence as `o`:
some times satisfy the presuppositions of a past tense and of the demonstrative restricting it,
(13), with the demonstrative's interval licensed and the assessment time placed by CATS. -/
def Admits (d : Demonstrative) (p : Position) (sister anterior : Bool) (o : Ordering) : Prop :=
  ∃ (τ₀ r J a u : NonemptyInterval ℤ) (t : Past), Licensed sister anterior p J τ₀ ∧
    Restricted t.cell d.cell a r J ∧ (t = .remote → a.Precedes u) ∧ Cats a u τ₀ ∧
      r.position τ₀ = o

/-- The positional generalization (45): a sentence with a final demonstrative overlaps the
preceding sentence; with an initial one it may follow it, overlap it only if the preceding
sentence is not a sister, and precede it only with *then* and an earlier time to pick out. -/
def Predicted (d : Demonstrative) (sister anterior : Bool) : Position → Ordering → Prop
  | .final, o => o = .eq
  | .initial, .gt => True
  | .initial, .eq => sister = false
  | .initial, .lt => d = .then ∧ (anterior = true ∨ sister = false)

instance (d : Demonstrative) (sister anterior : Bool) (p : Position) (o : Ordering) :
    Decidable (Predicted d sister anterior p o) := by
  cases p <;> cases o <;> unfold Predicted <;> infer_instance

@[simp] theorem gt_mem_initialPositions {sister anterior : Bool} :
    .gt ∈ initialPositions sister anterior := by
  cases sister <;> cases anterior <;> decide

theorem lt_mem_initialPositions {sister anterior : Bool} :
    .lt ∈ initialPositions sister anterior ↔ anterior = true := by
  cases sister <;> cases anterior <;> decide

theorem eq_mem_initialPositions {sister anterior : Bool} :
    .eq ∈ initialPositions sister anterior ↔ sister = false := by
  cases sister <;> cases anterior <;> decide

private theorem position_eq_of_le (hle : r ≤ J) (h : J.position τ₀ ≠ .eq) :
    r.position τ₀ = J.position τ₀ :=
  ((NonemptyInterval.position_eq_or_eq_eq_of_le hle).resolve_right h).symm

private theorem predicted_of_admits {d : Demonstrative} {p : Position} {sister anterior : Bool}
    {o : Ordering} : Admits d p sister anterior o → Predicted d sister anterior p o := by
  rintro ⟨τ₀, r, J, a, u, t, hJ, hres, hrem, hcats, rfl⟩
  have hnow : d = .now → ¬ r.Precedes τ₀ := by
    rintro rfl
    cases t
    · exact absurd hres not_restricted_now_past
    · exact not_precedes_of_cats hcats (presup_le.1 hres.1) (hrem rfl)
  cases p with
  | final =>
    cases hJ
    exact NonemptyInterval.position_eq_eq.2 (NonemptyInterval.overlaps_of_le hres.2.1)
  | initial =>
    change J.position τ₀ ∈ initialPositions sister anterior at hJ
    rcases hpos : J.position τ₀ with _ | _ | _ <;> rw [hpos] at hJ
    · have h := position_eq_of_le (τ₀ := τ₀) hres.2.1 (by rw [hpos]; decide)
      rw [hpos] at h
      rw [h]
      cases d
      · exact absurd (NonemptyInterval.position_eq_lt.1 h) (hnow rfl)
      · exact ⟨rfl, .inl (lt_mem_initialPositions.1 hJ)⟩
    · have hs := eq_mem_initialPositions.1 hJ
      rcases hr : r.position τ₀ with _ | _ | _
      · cases d
        · exact absurd (NonemptyInterval.position_eq_lt.1 hr) (hnow rfl)
        · exact ⟨rfl, .inr hs⟩
      · exact hs
      · trivial
    · rw [position_eq_of_le (τ₀ := τ₀) hres.2.1 (by rw [hpos]; decide), hpos]
      trivial

/-- An interval of `ℤ`. -/
private abbrev I (x y : ℤ) (h : x ≤ y := by decide) : NonemptyInterval ℤ := ⟨(x, y), h⟩

private theorem admits_final_now (sister anterior : Bool) :
    Admits .now .final sister anterior .eq :=
  ⟨I 0 1, I 0 1, I 0 1, I 0 1, I 2 2, .remote, rfl,
    ⟨presup_le.2 le_rfl, le_rfl, presup_le.2 le_rfl⟩, fun _ ↦ by decide, .inr fun _ ↦ .rfl,
    NonemptyInterval.position_self _⟩

private theorem admits_final_then (sister anterior : Bool) :
    Admits .then .final sister anterior .eq :=
  ⟨I 0 1, I 0 1, I 0 1, I 2 2, I 2 2, .past, rfl,
    ⟨presup_precedes.2 (by decide), le_rfl, presup_then.2 (by decide)⟩, nofun, .inl rfl,
    NonemptyInterval.position_self _⟩

private theorem admits_initial_now_gt (sister anterior : Bool) :
    Admits .now .initial sister anterior .gt :=
  ⟨I 0 1, I 2 3, I 2 3, I 0 3, I 4 4, .remote,
    show (I 2 3).position (I 0 1) ∈ _ by rw [show (I 2 3).position (I 0 1) = .gt by decide]; simp,
    ⟨presup_le.2 (NonemptyInterval.le_def.2 ⟨by decide, by decide⟩), le_rfl,
      presup_le.2 (NonemptyInterval.le_def.2 ⟨by decide, by decide⟩)⟩,
    fun _ ↦ by decide, .inr (forall_precedes_iff_iff_fst_eq.2 rfl), by decide⟩

private theorem admits_initial_now_eq (anterior : Bool) :
    Admits .now .initial false anterior .eq :=
  ⟨I 0 1, I 0 1, I 0 1, I 0 1, I 2 2, .remote,
    show (I 0 1).position (I 0 1) ∈ _ by
      rw [NonemptyInterval.position_self]; exact eq_mem_initialPositions.2 rfl,
    ⟨presup_le.2 le_rfl, le_rfl, presup_le.2 le_rfl⟩, fun _ ↦ by decide, .inr fun _ ↦ .rfl,
    NonemptyInterval.position_self _⟩

private theorem admits_initial_then_gt (sister anterior : Bool) :
    Admits .then .initial sister anterior .gt :=
  ⟨I 0 1, I 2 3, I 2 3, I 4 4, I 4 4, .past,
    show (I 2 3).position (I 0 1) ∈ _ by rw [show (I 2 3).position (I 0 1) = .gt by decide]; simp,
    ⟨presup_precedes.2 (by decide), le_rfl, presup_then.2 (by decide)⟩, nofun, .inl rfl,
    by decide⟩

private theorem admits_initial_then_eq (anterior : Bool) :
    Admits .then .initial false anterior .eq :=
  ⟨I 0 1, I 0 1, I 0 1, I 2 2, I 2 2, .past,
    show (I 0 1).position (I 0 1) ∈ _ by
      rw [NonemptyInterval.position_self]; exact eq_mem_initialPositions.2 rfl,
    ⟨presup_precedes.2 (by decide), le_rfl, presup_then.2 (by decide)⟩, nofun, .inl rfl,
    NonemptyInterval.position_self _⟩

private theorem admits_initial_then_lt_of_anterior (sister : Bool) :
    Admits .then .initial sister true .lt :=
  ⟨I 2 3, I 0 1, I 0 1, I 4 4, I 4 4, .past,
    show (I 0 1).position (I 2 3) ∈ _ by
      rw [show (I 0 1).position (I 2 3) = .lt by decide]; exact lt_mem_initialPositions.2 rfl,
    ⟨presup_precedes.2 (by decide), le_rfl, presup_then.2 (by decide)⟩, nofun, .inl rfl,
    by decide⟩

private theorem admits_initial_then_lt_of_not_sister (anterior : Bool) :
    Admits .then .initial false anterior .lt :=
  ⟨I 2 3, I 0 1, I 0 3, I 4 4, I 4 4, .past,
    show (I 0 3).position (I 2 3) ∈ _ by
      rw [show (I 0 3).position (I 2 3) = .eq by decide]; exact eq_mem_initialPositions.2 rfl,
    ⟨presup_precedes.2 (by decide), NonemptyInterval.le_def.2 ⟨by decide, by decide⟩,
      presup_then.2 (by decide)⟩, nofun, .inl rfl, by decide⟩

/-- The account derives the positional generalization (45). -/
theorem admits_iff {d : Demonstrative} {p : Position} {sister anterior : Bool} {o : Ordering} :
    Admits d p sister anterior o ↔ Predicted d sister anterior p o := by
  refine ⟨predicted_of_admits, fun h ↦ ?_⟩
  cases p with
  | final =>
    obtain rfl : o = .eq := h
    cases d
    exacts [admits_final_now sister anterior, admits_final_then sister anterior]
  | initial =>
    cases o with
    | gt => cases d; exacts [admits_initial_now_gt sister anterior,
        admits_initial_then_gt sister anterior]
    | eq =>
      obtain rfl : sister = false := h
      cases d; exacts [admits_initial_now_eq anterior, admits_initial_then_eq anterior]
    | lt =>
      obtain ⟨rfl, h | rfl⟩ := h
      · obtain rfl := h
        exact admits_initial_then_lt_of_anterior sister
      · exact admits_initial_then_lt_of_not_sister anterior

/-! ### The examples -/

/-- The relation to the preceding sentence that a reading names. -/
def readingRelation : List (String × Ordering) :=
  [("overlapping", .eq), ("forward-shifted", .gt), ("backshifted", .lt)]

/-- Whether an example's preceding sentence answers a sister subquestion. -/
def sisterOf (row : Datum) : Bool := row.feature? "sister" != some "no"

/-- Whether an example makes a time before the preceding sentence retrievable. -/
def anteriorOf (row : Datum) : Bool := row.feature? "anterior" == some "yes"

/-- A reading of an example is accepted exactly when the account admits it and, for an
overlapping reading, the aspect of the sentences allows overlap, as in Partee's (6). -/
theorem accepted_iff_admits : ∀ row ∈ Examples.all,
    ∀ d ∈ row.parse? "demonstrative" [("now", Demonstrative.now), ("then", .then)],
    ∀ p ∈ row.parse? "position" [("initial", Position.initial), ("final", .final)],
    ∀ reading ∈ row.readings, ∀ o ∈ readingRelation.lookup reading.1,
      (reading.2 = .acceptable ↔ Admits d p (sisterOf row) (anteriorOf row) o ∧
        ¬ (row.feature? "aspect" = some "state cannot overlap" ∧ o = .eq)) := by
  simp only [admits_iff]
  decide +kernel

end AnandToosarvandani2019
