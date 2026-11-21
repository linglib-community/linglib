module

public import Studies.IatridouEtAl2001

/-!
# Pancheva (2003): Aspectual Makeup of Perfect Participles and the Interpretations of the Perfect

Pancheva gives the perfect one meaning: a perfect time span of which the reference interval is a
final subinterval. The readings come from the viewpoint aspect the perfect embeds. The unbounded
aspect, the span inside the run time of an event, gives the universal perfect; the neutral, the
span overlapping an event that starts after it does, and the bounded, the run time properly
inside the span, give two experiential perfects; and a resultative aspect over telic predicates,
the span overlapping into the run time of the event's result state, gives the resultative
perfect. Greek lacks the universal perfect because its perfect does not embed the unbounded
aspect. When the span may start arbitrarily early the experiential and resultative perfects say
only how the eventuality or the result state stands to the right boundary of the reference
interval, and at a moment of reference the universal and the two experiential perfects are the
three perfects of the older account by Iatridou, Anagnostopoulou and Izvorski.

## Implementation notes

* The perfect is `Aspect.perfect` and the unbounded aspect `Aspect.unbounded`. The
  neutral relation of (7b) is strict, the interval having a point before every point of the
  event, so it is not Smith's neutral viewpoint `ViewpointType.neutral`, which lets the interval
  start with the event; and (7b) lets the interval end where the event starts, where Smith's
  reaches one of its stages (`overlapsFromBefore_neutral_incomparable`).
* The resultative takes a predicate of result states and their events, which only telic
  predicates denote, so an activity such as *run* in (5) has no resultative perfect by its type.
  The paper's formula (17) reads only the run time of the state.
* Theorems that let the perfect time span start before any given time assume that time has no
  first moment (`NoMinOrder`); without a perfect-level adverbial, which the paper's formulas do
  not include, the left boundary of the span is free.

## TODO

* The claim that (16a–b) are incompatible with the utterance time lying in the event time does
  not follow from (15b): an event ending exactly at the utterance time satisfies it
  (`bounded_experiential_of_ends_at_rb`), as footnote 8's remark on endpoints anticipates. What
  follows is that the event does not continue past it (`bounded_experiential_not_beyond_rb`).
* The spell-out tables (20)–(21), the sequence-of-tense contrasts (24)–(25) and (37)–(39), and
  the parallelism argument (31) are left in prose; the paper proposes no formal account of the
  latter two.
* Perfect-level adverbials such as *since 2000* in (1a) are not part of the paper's formulas.

## References

* [pancheva-2003]
* [iatridou-anagnostopoulou-izvorski-2001]
* [smith-1997]
-/

@[expose] public section

namespace Pancheva2003

open Aspect ModalLogic IntervalAlgebra Allen

open Event (τ)

variable {T E S : Type*} [LinearOrder T] [TemporalTrace E T] [TemporalTrace S T]

/-! ### The interval relations of (7b) and (17) -/

/-- The cell of the neutral aspect says how the run time `j` stands to the reference interval
`i`: the two overlap and `i` begins strictly before `j`. -/
def overlapsFromBefore : IntervalAlgebra := overlaps ⊓ .ofPred (·.fstFst = .gt)

/-- The cell of the resultative aspect says how the run time `j` of the result state stands to
the reference interval `i`: `i` begins strictly before `j`, the two overlap, and `j` ends strictly
after `i`. -/
def overlapsInto : IntervalAlgebra :=
  .ofPred fun r ↦ r.fstFst = .gt ∧ r.fstSnd ≠ .gt ∧ r.sndSnd = .gt

@[simp] theorem relation_mem_overlapsFromBefore {i j : NonemptyInterval T} :
    relation j i ∈ overlapsFromBefore ↔ i.Overlaps j ∧ i.fst < j.fst := by
  rw [overlapsFromBefore, mem_inf, relation_mem_overlaps, mem_ofPred]
  simp [relation, ofEndpoints, NonemptyInterval.Overlaps, compare_gt_iff_gt, and_comm]

@[simp] theorem relation_mem_overlapsInto {i j : NonemptyInterval T} :
    relation j i ∈ overlapsInto ↔ i.fst < j.fst ∧ j.fst ≤ i.snd ∧ i.snd < j.snd := by
  rw [overlapsInto, mem_ofPred]
  simp [relation, ofEndpoints, compare_gt_iff_gt]

theorem overlapsFromBefore_iff (i j : NonemptyInterval T) :
    relation j i ∈ overlapsFromBefore ↔ i.Overlaps j ∧ ∃ t ∈ i, t ∉ j ∧ ∀ t' ∈ j, t < t' := by
  rw [relation_mem_overlapsFromBefore]
  refine and_congr_right fun _ ↦ ⟨fun h ↦ ⟨i.fst, ?_, ?_, fun t' ht' ↦ ?_⟩, ?_⟩
  · exact NonemptyInterval.mem_def.2 ⟨le_rfl, i.fst_le_snd⟩
  · exact fun hm ↦ h.not_ge (NonemptyInterval.mem_def.1 hm).1
  · exact h.trans_le (NonemptyInterval.mem_def.1 ht').1
  · rintro ⟨t, ht, -, hlt⟩
    exact (NonemptyInterval.mem_def.1 ht).1.trans_lt
      (hlt j.fst (NonemptyInterval.mem_def.2 ⟨le_rfl, j.fst_le_snd⟩))

theorem overlapsInto_iff (i j : NonemptyInterval T) :
    relation j i ∈ overlapsInto ↔
      i.Overlaps j ∧ ∃ t t', t ∈ i ∧ t ∉ j ∧ t' ∈ j ∧ t' ∉ i ∧ t < t' := by
  rw [relation_mem_overlapsInto]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨⟨h₁.le.trans j.fst_le_snd, h₂⟩, i.fst, j.snd, ?_, ?_, ?_, ?_, ?_⟩
    · exact NonemptyInterval.mem_def.2 ⟨le_rfl, i.fst_le_snd⟩
    · exact fun hm ↦ h₁.not_ge (NonemptyInterval.mem_def.1 hm).1
    · exact NonemptyInterval.mem_def.2 ⟨j.fst_le_snd, le_rfl⟩
    · exact fun hm ↦ h₃.not_ge (NonemptyInterval.mem_def.1 hm).2
    · exact i.fst_le_snd.trans_lt h₃
  · rintro ⟨⟨-, h₂⟩, t, t', ht, htj, ht', ht'i, hlt⟩
    rw [NonemptyInterval.mem_def] at ht ht'
    refine ⟨?_, h₂, ?_⟩
    · by_contra h
      exact htj (NonemptyInterval.mem_def.2 ⟨(not_lt.1 h).trans ht.1, hlt.le.trans ht'.2⟩)
    · by_contra h
      exact ht'i (NonemptyInterval.mem_def.2 ⟨ht.1.trans hlt.le, ht'.2.trans (not_lt.1 h)⟩)

/-! ### The viewpoint aspects of (7b) and (17) -/

/-- The bounded aspect, (7b), holds where the run time of an event of the predicate is properly
contained in the reference interval. -/
def bounded (P : E → Prop) : NonemptyInterval T → Prop :=
  ◇[toSetRel IntervalAlgebra.lt] (Event.runTimes P)

/-- The neutral aspect, (7b), holds where the reference interval overlaps the run time of an
event of the predicate and begins strictly before it. -/
def neutral (P : E → Prop) : NonemptyInterval T → Prop :=
  ◇[toSetRel overlapsFromBefore] (Event.runTimes P)

/-- The resultative aspect, (17), holds of a predicate of result states and their events where
the reference interval overlaps into the run time of the result state. -/
def resultative (P : S → E → Prop) : NonemptyInterval T → Prop :=
  ◇[toSetRel overlapsInto] (Event.runTimes fun s ↦ ∃ e, P s e)

variable {P : E → Prop} {Q : S → E → Prop} {i : NonemptyInterval T} {t : T}

theorem bounded_iff : bounded P i ↔ ∃ e, τ e < i ∧ P e := by
  simp [bounded, Event.diamond_runTimes_iff]

theorem neutral_iff :
    neutral P i ↔ ∃ e, (i.Overlaps (τ e) ∧ i.fst < (τ e).fst) ∧ P e := by
  simp [neutral, Event.diamond_runTimes_iff]

omit [TemporalTrace E T] in
theorem resultative_iff : resultative Q i ↔
    ∃ e s, (i.fst < (τ s).fst ∧ (τ s).fst ≤ i.snd ∧ i.snd < (τ s).snd) ∧ Q s e := by
  simp only [resultative, Event.diamond_runTimes_iff, mem_toSetRel, relation_mem_overlapsInto]
  exact ⟨fun ⟨s, h, e, hQ⟩ ↦ ⟨e, s, h, hQ⟩, fun ⟨e, s, h, hQ⟩ ↦ ⟨s, h, e, hQ⟩⟩

-- footnote 8
theorem bounded_le_perfective (P : E → Prop) : bounded (T := T) P ≤ perfective P :=
  fun _ h ↦ let ⟨e, hlt, hP⟩ := bounded_iff.1 h; perfective_iff.2 ⟨e, hlt.le, hP⟩

theorem overlapsFromBefore_neutral_incomparable :
    ¬ (∀ i j : NonemptyInterval ℕ,
        relation j i ∈ overlapsFromBefore → relation j i ∈ ViewpointType.neutral.cell) ∧
      ¬ ∀ i j : NonemptyInterval ℕ,
        relation j i ∈ ViewpointType.neutral.cell → relation j i ∈ overlapsFromBefore := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := ViewpointType.relation_mem_cell_neutral.1 <|
      h ⟨(0, 1), by decide⟩ ⟨(1, 3), by decide⟩ (relation_mem_overlapsFromBefore.2 (by decide))
    revert this
    decide
  · have := relation_mem_overlapsFromBefore.1 <|
      h ⟨(1, 2), by decide⟩ ⟨(1, 3), by decide⟩
        (ViewpointType.relation_mem_cell_neutral.2 (by decide))
    revert this
    decide

/-! ### What each perfect asserts at the reference interval -/

/-- The universal perfect, (11), asserts the eventuality throughout the reference interval, and
conversely, since the unbounded aspect has the subinterval property. -/
theorem universal_iff_unbounded : perfect (unbounded P) i ↔ unbounded P i := by
  rw [perfect_eq_of_antitone (antitone_unbounded P)]

/-- The universal perfect holds at the right boundary of the reference interval, the time tense
locates. -/
theorem universal_at_rb (h : perfect (unbounded P) i) : ∃ e, P e ∧ i.snd ∈ τ e :=
  let ⟨e, hle, hP⟩ := unbounded_iff.1 (universal_iff_unbounded.1 h)
  ⟨e, hP, NonemptyInterval.mem_def.2
    ⟨(NonemptyInterval.le_def.1 hle).1.trans i.fst_le_snd, (NonemptyInterval.le_def.1 hle).2⟩⟩

-- (12)
theorem neutral_experiential_begun_by_rb (h : perfect (neutral P) i) :
    ∃ e, P e ∧ (τ e).fst ≤ i.snd :=
  let ⟨_, hf, hn⟩ := perfect_iff.1 h
  let ⟨e, hrel, hP⟩ := neutral_iff.1 hn
  ⟨e, hP, hf.2 ▸ hrel.1.2⟩

-- (15)
theorem bounded_experiential_ended_by_rb (h : perfect (bounded P) i) :
    ∃ e, P e ∧ (τ e).snd ≤ i.snd :=
  let ⟨_, hf, hb⟩ := perfect_iff.1 h
  let ⟨e, hlt, hP⟩ := bounded_iff.1 hb
  ⟨e, hP, hf.2 ▸ (NonemptyInterval.le_def.1 hlt.le).2⟩

omit [TemporalTrace E T] in
/-- The resultative perfect, (18), asserts the result state at the right boundary of the
reference interval, overlapping the reference interval and continuing past it. -/
theorem resultative_state_at_rb (h : perfect (resultative Q) i) :
    ∃ e s, Q s e ∧ i.snd ∈ τ s ∧ (τ s).Overlaps i ∧ i.snd < (τ s).snd :=
  let ⟨_, hf, hr⟩ := perfect_iff.1 h
  let ⟨e, s, hrel, hQ⟩ := resultative_iff.1 hr
  have h₁ : (τ s).fst ≤ i.snd := hf.2 ▸ hrel.2.1
  have h₂ : i.snd < (τ s).snd := hf.2 ▸ hrel.2.2
  ⟨e, s, hQ, NonemptyInterval.mem_def.2 ⟨h₁, h₂.le⟩, ⟨h₁, i.fst_le_snd.trans h₂.le⟩, h₂⟩

/-! ### The perfects when the span may start early

Without a perfect-level adverbial the left boundary of the span is free, and when time has no
first moment the experiential and resultative perfects reduce to conditions at the right
boundary of the reference interval. -/

section NoMin

variable [NoMinOrder T]

private theorem exists_span (i : NonemptyInterval T) (a : T) :
    ∃ pts : NonemptyInterval T, i.FinalSubinterval pts ∧ pts.fst < a := by
  obtain ⟨b, hb⟩ := exists_lt (min i.fst a)
  exact ⟨⟨(b, i.snd), (hb.le.trans (min_le_left _ _)).trans i.fst_le_snd⟩,
    ⟨hb.le.trans (min_le_left _ _), rfl⟩,
    hb.trans_le (min_le_right _ _)⟩

/-- The neutral experiential asserts exactly that an eventuality has begun by the right boundary
of the reference interval. -/
theorem neutral_experiential_iff : perfect (neutral P) i ↔ ∃ e, P e ∧ (τ e).fst ≤ i.snd := by
  refine ⟨neutral_experiential_begun_by_rb, fun ⟨e, hP, h⟩ ↦ ?_⟩
  obtain ⟨pts, hf, hlt⟩ := exists_span i (τ e).fst
  exact perfect_iff.2 ⟨pts, hf,
    neutral_iff.2 ⟨e, ⟨⟨hlt.le.trans (τ e).fst_le_snd, hf.2 ▸ h⟩, hlt⟩, hP⟩⟩

/-- The bounded experiential asserts exactly that an eventuality has ended by the right boundary
of the reference interval. -/
theorem bounded_experiential_iff : perfect (bounded P) i ↔ ∃ e, P e ∧ (τ e).snd ≤ i.snd := by
  refine ⟨bounded_experiential_ended_by_rb, fun ⟨e, hP, h⟩ ↦ ?_⟩
  obtain ⟨pts, hf, hlt⟩ := exists_span i (τ e).fst
  exact perfect_iff.2 ⟨pts, hf, bounded_iff.2 ⟨e, NonemptyInterval.lt_def.2
    ⟨NonemptyInterval.le_def.2 ⟨hlt.le, hf.2 ▸ h⟩, Or.inl hlt⟩, hP⟩⟩

omit [TemporalTrace E T] in
/-- The resultative perfect asserts exactly that a result state holds at the right boundary of
the reference interval and continues beyond it. -/
theorem resultative_perfect_iff :
    perfect (resultative Q) i ↔ ∃ e s, Q s e ∧ (τ s).fst ≤ i.snd ∧ i.snd < (τ s).snd := by
  refine ⟨fun h ↦ ?_, fun ⟨e, s, hQ, h₁, h₂⟩ ↦ ?_⟩
  · obtain ⟨e, s, hQ, hm, -, h₂⟩ := resultative_state_at_rb h
    exact ⟨e, s, hQ, (NonemptyInterval.mem_def.1 hm).1, h₂⟩
  · obtain ⟨pts, hf, hlt⟩ := exists_span i (τ s).fst
    exact perfect_iff.2 ⟨pts, hf, resultative_iff.2 ⟨e, s, ⟨hlt, hf.2 ▸ h₁, hf.2 ▸ h₂⟩, hQ⟩⟩

/-- The bounded aspect and the perfective give the same perfect, so the proper containment of
footnote 8 makes no difference. -/
theorem bounded_perfect_iff_perfective_perfect :
    perfect (bounded P) i ↔ perfect (perfective P) i := by
  refine ⟨perfect_mono (bounded_le_perfective P) i, fun h ↦ ?_⟩
  obtain ⟨e, hle, hP⟩ := perfect_perfective_iff.1 h
  exact bounded_experiential_iff.2 ⟨e, hP, hle⟩

-- (13)
theorem neutral_experiential_of_universal (h : perfect (unbounded P) i) :
    perfect (neutral P) i :=
  let ⟨e, hle, hP⟩ := unbounded_iff.1 (universal_iff_unbounded.1 h)
  neutral_experiential_iff.2 ⟨e, hP, (NonemptyInterval.le_def.1 hle).1.trans i.fst_le_snd⟩

-- (15b), (12b)
theorem neutral_experiential_of_bounded (h : perfect (bounded P) i) :
    perfect (neutral P) i :=
  let ⟨e, hP, hle⟩ := bounded_experiential_ended_by_rb h
  neutral_experiential_iff.2 ⟨e, hP, (τ e).fst_le_snd.trans hle⟩

/-! #### (13) against (16) -/

-- (13)
theorem neutral_experiential_of_ongoing {e₀ : E} (h₁ : (τ e₀).fst ≤ t) (h₂ : t < (τ e₀).snd) :
    perfect (neutral (· = e₀)) (.pure t) ∧ t ∈ τ e₀ :=
  ⟨neutral_experiential_iff.2 ⟨e₀, rfl, h₁⟩, NonemptyInterval.mem_def.2 ⟨h₁, h₂.le⟩⟩

-- (13)
theorem neutral_experiential_of_over {e₀ : E} (h : (τ e₀).snd < t) :
    perfect (neutral (· = e₀)) (.pure t) ∧ t ∉ τ e₀ :=
  ⟨neutral_experiential_iff.2 ⟨e₀, rfl, (τ e₀).fst_le_snd.trans h.le⟩,
    fun hm ↦ h.not_ge (NonemptyInterval.mem_def.1 hm).2⟩

omit [NoMinOrder T] in
-- (16)
theorem bounded_experiential_not_beyond_rb (h : perfect (bounded P) i) :
    ∃ e, P e ∧ ¬ i.snd < (τ e).snd :=
  let ⟨e, hP, hle⟩ := bounded_experiential_ended_by_rb h
  ⟨e, hP, hle.not_gt⟩

/-- The bounded experiential holds of an eventuality ending at the moment of reference, so (16)
allows the utterance time inside the event time. -/
theorem bounded_experiential_of_ends_at_rb {e₀ : E} (h : (τ e₀).snd = t) :
    perfect (bounded (· = e₀)) (.pure t) ∧ t ∈ τ e₀ :=
  ⟨bounded_experiential_iff.2 ⟨e₀, rfl, h.le⟩,
    NonemptyInterval.mem_def.2 ⟨(τ e₀).fst_le_snd.trans h.le, h.ge⟩⟩

/-! #### Consistency with Iatridou, Anagnostopoulou and Izvorski -/

omit [NoMinOrder T] in
theorem perfect_inclusive_unbounded_iff :
    perfect (inclusive (unbounded P)) (.pure t) ↔ ∃ e, P e ∧ (τ e).fst ≤ t := by
  rw [perfect_pure_iff]
  constructor
  · rintro ⟨pts, hRB, hinc⟩
    obtain ⟨e, hov, hP⟩ := IatridouEtAl2001.inclusive_unbounded_iff.1 hinc
    exact ⟨e, hP, hov.1.trans_eq hRB⟩
  · rintro ⟨e, hP, h⟩
    exact ⟨⟨(min t (τ e).fst, t), min_le_left _ _⟩, rfl,
      IatridouEtAl2001.inclusive_unbounded_iff.2
        ⟨e, ⟨h, (min_le_right _ _).trans (τ e).fst_le_snd⟩, hP⟩⟩

/-- At a moment of reference the neutral experiential is the older account's inclusive perfect
of an unbounded eventuality. -/
theorem neutral_experiential_iff_inclusive_unbounded :
    perfect (neutral P) (.pure t) ↔ perfect (inclusive (unbounded P)) (.pure t) := by
  rw [perfect_inclusive_unbounded_iff, neutral_experiential_iff]; rfl

/-- At a moment of reference the bounded experiential is the older account's inclusive perfect
of a bounded eventuality. -/
theorem bounded_experiential_iff_inclusive_bounded :
    perfect (bounded P) (.pure t) ↔ perfect (inclusive (perfective P)) (.pure t) := by
  rw [bounded_perfect_iff_perfective_perfect, IatridouEtAl2001.inclusive_perfective]

end NoMin

/-- At a moment of reference the universal perfect is the older account's durative perfect of an
unbounded eventuality, with the covert adverbial. -/
theorem universal_iff_durative_unbounded :
    perfect (unbounded P) (.pure t) ↔ perfect (durative (unbounded P)) (.pure t) := by
  rw [IatridouEtAl2001.durative_unbounded]

/-! ### Greek and Portuguese -/

/-- A perfect over the neutral aspect never has its span inside the run time of its eventuality,
so a perfect that cannot embed the unbounded aspect, as in Greek, has no universal reading. -/
theorem neutral_span_not_covered (h : perfect (neutral P) i) :
    ∃ pts, i.FinalSubinterval pts ∧ ∃ e, P e ∧ ¬ pts ≤ τ e :=
  let ⟨pts, hf, hn⟩ := perfect_iff.1 h
  let ⟨e, hrel, hP⟩ := neutral_iff.1 hn
  ⟨pts, hf, e, hP, fun hle ↦ hrel.2.not_ge (NonemptyInterval.le_def.1 hle).1⟩

/-- A perfect over the bounded aspect never has its span inside the run time of its eventuality.
-/
theorem bounded_span_not_covered (h : perfect (bounded P) i) :
    ∃ pts, i.FinalSubinterval pts ∧ ∃ e, P e ∧ ¬ pts ≤ τ e :=
  let ⟨pts, hf, hb⟩ := perfect_iff.1 h
  let ⟨e, hlt, hP⟩ := bounded_iff.1 hb
  ⟨pts, hf, e, hP, hlt.not_ge⟩

theorem universal_not_ended_before_rb (h : perfect (unbounded P) i) :
    ∃ e, P e ∧ ¬ (τ e).snd < i.snd :=
  let ⟨e, hP, hm⟩ := universal_at_rb h
  ⟨e, hP, (NonemptyInterval.mem_def.1 hm).2.not_gt⟩

end Pancheva2003
