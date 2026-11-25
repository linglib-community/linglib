module

public import Linglib.Semantics.Aspect.SubintervalProperty

/-!
# Iatridou et al. (2001): Observations about the form and meaning of the perfect

Iatridou, Anagnostopoulou and Izvorski give the perfect a perfect time span, whose right boundary
tense sets and whose left boundary the argument of a perfect-level adverbial sets, in or
throughout which there is a bounded or unbounded eventuality. The adverbial is read inclusive or
durative, quantifying over the subintervals of the span, and the aspect of the participle makes
the eventuality bounded, the perfective, or unbounded, the imperfective, the progressive and the
Bulgarian neutral. The universal perfect is the durative reading of an unbounded eventuality and
holds at both boundaries by assertion; the inclusive reading is silent about the boundaries,
which is why an unmodified perfect, whose covert adverbial is inclusive, is never universal and
why the anteriority of the present perfect is derived rather than encoded. A bounded eventuality
that takes time holds throughout no span, so a perfect on a perfective participle, as in Greek,
has no universal perfect, except where an activity fills the span exactly.

## Implementation notes

* The features [unbounded] and [bounded] of the paper's footnote 5 are `Aspect.unbounded`, the
  span inside the run time of an event, and `Aspect.perfective`, the run time inside the span. The
  readings of the adverbial are `Temporal.durative` and `Temporal.inclusive`, quantification over
  the subintervals of the span, which the paper phrases both as every subinterval and as the
  points of the span. Over subintervals the durative unbounded reading is one event containing
  the span, the last paraphrase in (18b).
* The paper glosses *inclusive* as properly included in prose and writes plain existential
  quantification over the span in (18e) and (19c); the formulas are followed, and the
  consequence the prose draws, that neither boundary is asserted to be part of the eventuality,
  is `inclusive_silent_at_rb`.
* The adverbial classes of (16), the two levels of adverbials and the position of *for*,
  (23)–(24), are lexical and syntactic premises. Perfect-level *since t₀* admits the spans
  starting at `t₀` under either reading; *ever since*, *at least since*, *always* and
  perfect-level *for* are durative; *lately* and the covert adverbial are inclusive; and a
  sentence-initial *for* is perfect-level because it has merged above the eventuality. The study
  states the consequences of the readings, not the classification.
* The Greek perfect participle is built on the perfective stem only, the Bulgarian imperfective
  and neutral participles are unbounded, and in English the progressive realizes [unbounded] on
  nonstatives while statives are nonprogressive under either feature, (42). These enter as the
  aspect operator the theorems take. The neutral is the paper's [unbounded] participle, not
  Smith's neutral viewpoint `ViewpointType.neutral`, whose definition the paper finds unclear.

## TODO

* Vlach's stativity test separates the Bulgarian neutral, which fails it, (49a), from the
  imperfective, though both have the subinterval property; the test turns on the framing of a
  *when*-clause, which footnote 5 says the interval features do not predict.
* The Greek and Bulgarian participle facts belong in their languages' language files once these
  record the aspect of the perfect participle.
* The individual-level facts (8) and (25)–(26), the reduced relatives of the addendum and the
  account of sentence-initial *for* by Merge height are syntactic and left in prose.

## References

* [iatridou-anagnostopoulou-izvorski-2001]
* [mittwoch-1988]
* [vlach-1993]
* [dowty-1979]
* [smith-1997]
-/

public section

namespace IatridouEtAl2001

open Event (τ)

open Aspect Temporal

variable {T E : Type*} [LinearOrder T] [TemporalTrace E T]
  {p : NonemptyInterval T → Prop} {P : E → Prop} {i : NonemptyInterval T} {t t₀ : T}

/-! ### The four expansions of (43)

The perfect asserts a span in or throughout which there is a bounded or unbounded eventuality,
(43), and the four combinations are (44a–d). -/

-- (44a)
theorem durative_unbounded : durative (unbounded P) = unbounded P :=
  durative_eq_of_antitone (antitone_unbounded P)

-- (44b)
theorem inclusive_unbounded_iff :
    inclusive (unbounded P) i ↔ ∃ e, (τ e).Overlaps i ∧ P e :=
  Aspect.inclusive_unbounded_iff

-- (44c)
theorem inclusive_perfective : inclusive (perfective P) = perfective P :=
  inclusive_inclusive _

-- (44d)
theorem not_durative_perfective (h : ∀ e, P e → (τ e).fst < (τ e).snd) :
    ¬ durative (perfective P) i := fun hd ↦
  let ⟨e, hle, hP⟩ := perfective_iff.1 (durative_iff.1 hd (.pure i.fst)
    (NonemptyInterval.le_def.2 ⟨le_rfl, i.fst_le_snd⟩))
  (h e hP).not_ge ((NonemptyInterval.le_def.1 hle).2.trans (NonemptyInterval.le_def.1 hle).1)

-- (44d)
theorem durative_perfective_of_eq (hP : HasSubintervalProperty P) {e : E} (he : P e)
    (hτ : τ e = i) : durative (perfective P) i :=
  durative_iff.2 fun j hj ↦
    let ⟨e', hτ', hP'⟩ := hasSubintervalProperty_iff_witnesses.1 hP e he j (hτ ▸ hj)
    perfective_iff.2 ⟨e', hτ'.le, hP'⟩

/-! ### Point 1: the universal perfect at both boundaries -/

theorem durative_at_rb (h : perfect (durative p) (.pure t)) : p (.pure t) :=
  let ⟨pts, hrb, hd⟩ := perfect_pure_iff.1 h
  durative_iff.1 hd _ (NonemptyInterval.le_def.2 ⟨hrb ▸ pts.fst_le_snd, hrb.ge⟩)

theorem durative_at_lb (h : perfect ((fun pts ↦ pts.fst = t₀) ⊓ durative p) (.pure t)) :
    p (.pure t₀) :=
  let ⟨pts, _, hlb, hd⟩ := perfect_pure_iff.1 h
  durative_iff.1 hd _ (NonemptyInterval.le_def.2 ⟨hlb.le, hlb ▸ pts.fst_le_snd⟩)

theorem unbounded_pure_iff : unbounded P (.pure t) ↔ ∃ e, P e ∧ t ∈ τ e :=
  unbounded_iff.trans
    ⟨fun ⟨e, hle, hP⟩ ↦ ⟨e, hP, NonemptyInterval.mem_def.2 (NonemptyInterval.le_def.1 hle)⟩,
      fun ⟨e, hP, ht⟩ ↦ ⟨e, NonemptyInterval.le_def.2 (NonemptyInterval.mem_def.1 ht), hP⟩⟩

/-- The universal perfect asserts the eventuality at the right boundary, making (6a–b)
contradictions, in the past and future perfect too (7). -/
theorem universal_at_rb (h : perfect (durative (unbounded P)) (.pure t)) : ∃ e, P e ∧ t ∈ τ e :=
  unbounded_pure_iff.1 (durative_at_rb h)

/-- With *since t₀* the universal perfect holds at `t₀`, the observation of [mittwoch-1988]. -/
theorem universal_at_lb
    (h : perfect ((fun pts ↦ pts.fst = t₀) ⊓ durative (unbounded P)) (.pure t)) :
    ∃ e, P e ∧ t₀ ∈ τ e :=
  unbounded_pure_iff.1 (durative_at_lb h)

-- (2a), (18a)
theorem universal_of_covers {e : E} (he : P e) (h₀ : t₀ ≤ t) (h₁ : (τ e).fst ≤ t₀)
    (h₂ : t ≤ (τ e).snd) : perfect ((fun pts ↦ pts.fst = t₀) ⊓ durative (unbounded P)) (.pure t) :=
  perfect_pure_iff.2 ⟨⟨(t₀, t), h₀⟩, rfl, rfl, durative_iff.2 fun _ hj ↦
    unbounded_iff.2 ⟨e, hj.trans (NonemptyInterval.le_def.2 ⟨h₁, h₂⟩), he⟩⟩

/-! ### Point 2: an unmodified perfect is silent about the right boundary -/

/-- The inclusive perfect holds of an eventuality that ended before the time of tense, so *She has
been sick, but she is fine now* is consistent ((9)–(12), (15)). -/
theorem inclusive_silent_at_rb {e₀ : E} (h : (τ e₀).snd < t) :
    perfect (inclusive (unbounded (· = e₀))) (.pure t) ∧ ∀ e, e = e₀ → t ∉ τ e :=
  ⟨perfect_pure_iff.2 ⟨⟨((τ e₀).fst, t), (τ e₀).fst_le_snd.trans h.le⟩, rfl,
      inclusive_iff.2 ⟨τ e₀, NonemptyInterval.le_def.2 ⟨le_rfl, h.le⟩,
        unbounded_iff.2 ⟨e₀, le_rfl, rfl⟩⟩⟩,
    fun _ he ht ↦ (NonemptyInterval.mem_def.1 ht).2.not_gt (he ▸ h)⟩

/-- An unmodified perfect does not entail the universal perfect, which is therefore never its
reading. -/
theorem unmodified_not_universal {e₀ : E} (h : (τ e₀).snd < t) :
    ¬ ∀ P : E → Prop, perfect (inclusive (unbounded P)) (.pure t) →
      perfect (durative (unbounded P)) (.pure t) :=
  fun hall ↦
  let ⟨hperf, hnot⟩ := inclusive_silent_at_rb h
  let ⟨e, he, ht⟩ := universal_at_rb (hall _ hperf)
  hnot e he ht

/-! ### Point 3: the span is not the E–R interval -/

/-- With *since 1991* the span starts in 1991 though its only eventuality lies in the fall of 1993
(28). -/
theorem span_lb_before_event {lb : T} {e₀ : E} (h₁ : lb < (τ e₀).fst) (h₂ : (τ e₀).snd ≤ t) :
    perfect ((fun pts ↦ pts.fst = lb) ⊓ inclusive (perfective (· = e₀))) (.pure t) :=
  perfect_pure_iff.2 ⟨⟨(lb, t), h₁.le.trans ((τ e₀).fst_le_snd.trans h₂)⟩, rfl, rfl,
    inclusive_iff.2 ⟨τ e₀, NonemptyInterval.le_def.2 ⟨h₁.le, h₂⟩,
      perfective_iff.2 ⟨e₀, le_rfl, rfl⟩⟩⟩

/-! ### Point 4: the aspect of the participle -/

/-- A perfective participle on a predicate whose eventualities take time has no universal perfect,
in Greek (30) and (34), Bulgarian (35) and English (41). -/
theorem no_universal_of_perfective (h : ∀ e, P e → (τ e).fst < (τ e).snd) :
    ¬ perfect (durative (perfective P)) (.pure t) :=
  fun hp ↦ let ⟨_, _, hd⟩ := perfect_pure_iff.1 hp; not_durative_perfective h hd

/-- A perfective activity with *apo 1990 mexri tora* 'from 1990 until now' is true when an
eventuality fills the span exactly (45). -/
theorem bounded_activity_fills {e : E} (hP : HasSubintervalProperty P) (he : P e)
    (h₀ : t₀ ≤ t) (hτ : τ e = ⟨(t₀, t), h₀⟩) :
    perfect ((fun pts ↦ pts.fst = t₀) ⊓ durative (perfective P)) (.pure t) ∧
      ∃ e', P e' ∧ t ∈ τ e' :=
  have hd := durative_perfective_of_eq hP he hτ
  ⟨perfect_pure_iff.2 ⟨⟨(t₀, t), h₀⟩, rfl, rfl, hd⟩,
    let ⟨e', hτ', hP'⟩ := perfective_pure_iff.1 (durative_at_rb (perfect_pure_iff.2 ⟨_, rfl, hd⟩))
    ⟨e', hP', hτ' ▸ NonemptyInterval.mem_pure_self t⟩⟩

/-! ### Point 5: anteriority derived -/

/-- An experiential perfect ends its eventuality by the time of tense (1). -/
theorem experiential_ends_by_rb (h : perfect (inclusive (perfective P)) (.pure t)) :
    ∃ e, P e ∧ (τ e).snd ≤ t :=
  let ⟨_, hrb, hi⟩ := perfect_pure_iff.1 h
  let ⟨_, hj, hp⟩ := inclusive_iff.1 hi
  let ⟨e, hle, hP⟩ := perfective_iff.1 hp
  ⟨e, hP, hrb ▸ (NonemptyInterval.le_def.1 (hle.trans hj)).2⟩

/-- The universal perfect is not anterior, since its eventuality has not ended at the time of
tense, so an anteriority operator in the perfect would make it underivable. -/
theorem universal_not_anterior (h : perfect (durative (unbounded P)) (.pure t)) :
    ∃ e, P e ∧ ¬ (τ e).snd < t :=
  let ⟨e, hP, ht⟩ := universal_at_rb h
  ⟨e, hP, (NonemptyInterval.mem_def.1 ht).2.not_gt⟩

/-- In the future perfect the right boundary follows the utterance time `now`, and the
eventuality may end before `now` or start after it. -/
theorem future_perfect_underspecified {now : T} {e₁ e₂ : E} (h₁ : (τ e₁).snd < now)
    (h₂ : now < (τ e₂).fst) (h₂' : (τ e₂).snd ≤ t) :
    (∃ P : E → Prop, perfect (inclusive (perfective P)) (.pure t) ∧ ∀ e, P e → (τ e).snd < now) ∧
      ∃ P : E → Prop, perfect (inclusive (perfective P)) (.pure t) ∧ ∀ e, P e → now < (τ e).fst :=
  have hn : now < t := h₂.trans_le ((τ e₂).fst_le_snd.trans h₂')
  have key : ∀ e₀ : E, (τ e₀).snd ≤ t → perfect (inclusive (perfective (· = e₀))) (.pure t) :=
    fun e₀ h ↦ perfect_pure_iff.2 ⟨⟨((τ e₀).fst, t), (τ e₀).fst_le_snd.trans h⟩, rfl,
      inclusive_iff.2 ⟨τ e₀, NonemptyInterval.le_def.2 ⟨le_rfl, h⟩,
        perfective_iff.2 ⟨e₀, le_rfl, rfl⟩⟩⟩
  ⟨⟨(· = e₁), key e₁ (h₁.trans hn).le, fun _ he ↦ he ▸ h₁⟩,
    ⟨(· = e₂), key e₂ h₂', fun _ he ↦ he ▸ h₂⟩⟩

end IatridouEtAl2001
