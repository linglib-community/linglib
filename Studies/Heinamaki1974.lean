module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Aspect.Defs
public import Linglib.Fragments.English.TemporalConnectives
public import Linglib.Data.Examples.Heinamaki1974
public import Linglib.Data.Examples.Readers

/-!
# Heinämäki (1974): Semantics of English Temporal Connectives

A sentence specifies an interval, which for an achievement is a moment, and a temporal connective
relates the interval $J$ of its main clause to the interval $K$ of its temporal clause through
their initial and final points and a reference point $\mathrm{tr}$, the final point of an
accomplishment and the initial point otherwise. *Before* is thereby transitive and asymmetric
while *after* in general is neither, and [*A before B* and *B after A* are converses exactly when
$K$ is a moment](##forall_before_iff_after_iff_isPoint). The co-temporal connectives come apart:
[*as long as* strengthens *while*](##not_forall_while_imp_asLongAs), which asks only for overlap,
and [*as soon as* strengthens *after*](##not_forall_after_imp_asSoonAs), since it speaks of where
the main clause begins. The formulas [fit the paper's judgments of *while*, *as long as* and
*until*](##rows_predicted), but for the accomplishment main clauses of *as long as* and
*until*.

## Implementation notes

* A clause carries the intervals it specifies, its `Clause.intervals`, "and no shorter or longer
  stretch of time", so these are the maximal intervals and not the run times of
  `Semantics/Tense/RunTimes.lean`, which a state closes under subintervals.
* The thesis's "non-durative" (p. 25) is the achievement, with the "fast accomplishment" counted
  among achievements here. Its "durative" is `Durative`, a state or an activity, narrower than
  `VendlerClass.duration`, which an accomplishment shares.
* Intervals are closed, so *until* has the final point of (12) and not the alternative of a final
  bound (p. 123), and *A until B* reduces to $\mathrm{tr}(B)$ falling within $J$.
* The speakers' variants are left out: *before* with $\mathrm{tr}(A) < \mathrm{tr}(B)$ for an
  accomplishment temporal clause (p. 73), *after* with $J' = J$ for an accomplishment main clause
  (128), and the single-event *whenever* of (36), which quantifies over possible times.
* Non-factual *before* (§4.2.2), in which $B$ never holds, and the implicatures of chapter VI are
  not formalized.

## References

* [heinamaki-1974]
-/

@[expose] public section

namespace Heinamaki1974

open Aspect Tense NonemptyInterval

/-! ### Clauses and reference points -/

/-- A durative is a state or an activity (p. 25). -/
def Durative (c : VendlerClass) : Prop := c = .state ∨ c = .activity

instance : DecidablePred Durative := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- A clause of a structure *A connective B*: its situation type, the intervals it specifies, of
which only an achievement's are moments (pp. 25–26), and whether it is in the perfect. -/
structure Clause (T : Type*) [LE T] where
  /-- The situation type of the clause. -/
  vendler : VendlerClass
  /-- The intervals the clause specifies. -/
  intervals : Set (NonemptyInterval T)
  /-- An interval of the clause is a moment exactly when its class takes no time. -/
  isPoint_iff : ∀ i ∈ intervals, i.IsPoint ↔ vendler.duration = .punctual
  /-- The clause is in the perfect. -/
  perfect : Prop := False

/-- The context a sentence is evaluated in. -/
structure Context (T : Type*) [LT T] where
  /-- The present moment, the thesis's `tp`. -/
  now : T
  /-- The final point of the period of *since*: the present moment, the time of the narrative, or
  the time of an adverb in the main clause (63). -/
  final : T
  /-- The relation "immediately after", which is fuzzy and fixed by the context (p. 110). -/
  ImmediatelyAfter : T → T → Prop
  /-- What is immediately after a moment is after it. -/
  lt_of_immediatelyAfter : ∀ {s t}, ImmediatelyAfter s t → t < s

section Preorder

variable {T : Type*} [Preorder T]

/-- The present moment lies outside the interval whose endpoints are the reference points `s` and
`t` (p. 74), the condition (iv) of the formulas. -/
def Context.Outside (ctx : Context T) (s t : T) : Prop := ctx.now < s ∨ t < ctx.now

/-- The reference point `tr` (38) of an interval is its final point if an accomplishment defines
it, and otherwise its initial point. -/
def tr : VendlerClass → NonemptyInterval T → T
  | .accomplishment, i => i.snd
  | _, i => i.fst

variable {a b c : VendlerClass} {i J K L : NonemptyInterval T}

@[simp] theorem tr_accomplishment : tr .accomplishment i = i.snd := rfl

theorem tr_of_ne (h : c ≠ .accomplishment) : tr c i = i.fst := by
  cases c <;> first | rfl | exact absurd rfl h

theorem fst_le_tr (c : VendlerClass) (i : NonemptyInterval T) : i.fst ≤ tr c i := by
  cases c <;> first | exact le_rfl | exact i.fst_le_snd

theorem tr_le_snd (c : VendlerClass) (i : NonemptyInterval T) : tr c i ≤ i.snd := by
  cases c <;> first | exact le_rfl | exact i.fst_le_snd

-- A moment could be grouped with duratives or accomplishments, p. 72.
theorem tr_of_isPoint (h : i.IsPoint) (c : VendlerClass) : tr c i = i.fst := by
  cases c <;> first | rfl | exact h.symm

/-! ### The truth conditions -/

/-- The relation of *A before B* (39): the reference point of `A` precedes the start of `B`. -/
def Before (a : VendlerClass) (J K : NonemptyInterval T) : Prop := tr a J < K.fst

/-- The relation of *A after B* (128): some subinterval of `J` follows the reference point of
`B`. -/
def After (b : VendlerClass) (J K : NonemptyInterval T) : Prop := ∃ J' ≤ J, tr b K < J'.fst

/-- The relation of *A as soon as B* (136): the start of `A` is immediately after the reference
point of `B`, with the present moment outside the two. -/
def AsSoonAs (ctx : Context T) (b : VendlerClass) (J K : NonemptyInterval T) : Prop :=
  ctx.ImmediatelyAfter J.fst (tr b K) ∧ ctx.Outside (tr b K) J.fst

/-- Two intervals are co-temporal when they share a subinterval that an accomplishment's interval
coincides with, the condition common to (26iii.a) and (80iii). -/
def Cotemporal (a b : VendlerClass) (J K : NonemptyInterval T) : Prop :=
  ∃ I, I ≤ J ∧ I ≤ K ∧ (a = .accomplishment → J = I) ∧ (b = .accomplishment → K = I)

/-- The relation of *A when B* (26): co-temporal if either clause is durative, and otherwise
successive, with `B` first. -/
def When (a b : VendlerClass) (J K : NonemptyInterval T) : Prop :=
  (Durative a ∨ Durative b → Cotemporal a b J K) ∧ (¬ Durative a ∧ ¬ Durative b → K.snd < J.fst)

/-- The relation of *A while B* (80): co-temporal, with `K` not a moment. -/
def While (a b : VendlerClass) (J K : NonemptyInterval T) : Prop :=
  ¬ K.IsPoint ∧ Cotemporal a b J K

/-- The relation of *A as long as B* (93): neither is a moment and `K` lies within `J`. -/
def AsLongAs (J K : NonemptyInterval T) : Prop := ¬ J.IsPoint ∧ ¬ K.IsPoint ∧ K ≤ J

/-- The relation of *A until B* (12): `J` is not a moment and a subinterval of it ends at the
reference point of `B`, with the present moment outside the two. -/
def Until (ctx : Context T) (b : VendlerClass) (J K : NonemptyInterval T) : Prop :=
  ¬ J.IsPoint ∧ ∃ J' ≤ J, J'.snd = tr b K ∧ ctx.Outside J'.fst (tr b K)

/-- The relation of *A since B* (63): an interval `J'` contains or lies within `J`, begins with
`K` if both clauses are durative and perfect, at the end of `K` if `B` is an accomplishment, and
otherwise within `K`, and ends at the final point of the context, after the present moment has
passed its start. -/
def Since (ctx : Context T) (a b : VendlerClass) (perfect : Prop) (J K : NonemptyInterval T) :
    Prop :=
  ∃ J', (J' ≤ J ∨ J ≤ J') ∧
    (perfect ∧ Durative a ∧ Durative b → J'.fst = K.fst ∧ J' ≤ J ∧ J' ≤ K) ∧
    (b = .accomplishment → J'.fst = K.snd) ∧
    (¬ (perfect ∧ Durative a ∧ Durative b) ∧ b ≠ .accomplishment → J'.fst ∈ K) ∧
    J'.snd = ctx.final ∧ J'.fst < ctx.now

/-- The relation `R` holds of an interval of each clause, (i) and (ii) of the formulas. -/
def Clause.AtSome (A B : Clause T) (R : NonemptyInterval T → NonemptyInterval T → Prop) : Prop :=
  ∃ J ∈ A.intervals, ∃ K ∈ B.intervals, R J K

/-- The truth conditions of a sentence *A connective B* whose connective lexicalizes the relation.
*Before* and *after* carry the conditions of (46) and (132), and *whenever* is *every time when*
(p. 42). -/
def Holds (ctx : Context T) : Connective.Relation → Clause T → Clause T → Prop
  | .before, A, B => A.AtSome B fun J K ↦
      Before A.vendler J K ∧ ctx.Outside (tr A.vendler J) K.fst
  | .after, A, B => A.AtSome B fun J K ↦
      ∃ J' ≤ J, tr B.vendler K < J'.fst ∧ ctx.Outside (tr B.vendler K) J'.snd
  | .asSoonAs, A, B => A.AtSome B (AsSoonAs ctx B.vendler)
  | .when_, A, B => A.AtSome B (When A.vendler B.vendler)
  | .whenever, A, B => ∀ K ∈ B.intervals, ∃ J ∈ A.intervals, When A.vendler B.vendler J K
  | .while_, A, B => A.AtSome B (While A.vendler B.vendler)
  | .asLongAs, A, B => A.AtSome B AsLongAs
  | .until_, A, B => A.AtSome B (Until ctx B.vendler)
  | .since, A, B => A.AtSome B (Since ctx A.vendler B.vendler (A.perfect ∧ B.perfect))

/-! ### Before and after -/

theorem after_iff : After b J K ↔ tr b K < J.snd :=
  ⟨fun ⟨_, hJ', h⟩ ↦ h.trans_le (fst_le_snd _ |>.trans (le_def.1 hJ').2),
    fun h ↦ ⟨pure J.snd, le_def.2 ⟨J.fst_le_snd, le_rfl⟩, h⟩⟩

-- p. 113
theorem Before.trans (h₁ : Before a J K) (h₂ : Before b K L) : Before a J L :=
  h₁.trans_le (fst_le_tr b K) |>.trans h₂

-- p. 113
theorem Before.not_before (h₁ : Before a J K) : ¬ Before b K J :=
  fun h₂ ↦ lt_irrefl _ <| (h₁.trans h₂).trans_le (fst_le_tr a J)

-- p. 113
theorem Before.after (h : Before a J K) : After a K J :=
  after_iff.2 (h.trans_le K.fst_le_snd)

-- p. 113: when `K` is a moment, *after* is transitive, its main clauses being moments.
theorem After.trans (hK : K.IsPoint) (h₁ : After b J K) (h₂ : After c K L) : After c J L := by
  rw [after_iff] at *
  rw [tr_of_isPoint hK] at h₁
  rw [← hK] at h₂
  exact h₂.trans h₁

-- p. 113
theorem After.not_after (hJ : J.IsPoint) (hK : K.IsPoint) (h : After b J K) : ¬ After a K J := by
  rw [after_iff, tr_of_isPoint hK] at h
  rw [after_iff, tr_of_isPoint hJ, ← hK]
  rw [← hJ] at h
  exact h.not_gt

-- (144)
theorem not_forall_after_trans :
    ¬ ∀ J K L : NonemptyInterval ℤ, After .state J K → After .state K L → After .state J L := by
  intro h
  have := h ⟨(0, 2), by decide⟩ ⟨(1, 6), by decide⟩ ⟨(4, 5), by decide⟩
    (after_iff.2 (by decide)) (after_iff.2 (by decide))
  exact absurd (after_iff.1 this) (by decide)

-- (144)
theorem exists_after_and_after :
    ∃ K L : NonemptyInterval ℤ, After .state K L ∧ After .state L K :=
  ⟨⟨(1, 6), by decide⟩, ⟨(4, 5), by decide⟩, after_iff.2 (by decide), after_iff.2 (by decide)⟩

/-! ### When, while and as long as -/

theorem While.when (h : Durative a ∨ Durative b) (hw : While a b J K) : When a b J K :=
  ⟨fun _ ↦ hw.2, fun h' ↦ absurd h (not_or.2 h')⟩

theorem AsLongAs.while (ha : a ≠ .accomplishment) (h : AsLongAs J K) : While a b J K :=
  ⟨h.2.1, K, h.2.2, le_rfl, (absurd · ha), fun _ ↦ rfl⟩

/-! ### As soon as -/

theorem AsSoonAs.tr_lt {ctx : Context T} (h : AsSoonAs ctx b J K) : tr b K < J.fst :=
  ctx.lt_of_immediatelyAfter h.1

theorem AsSoonAs.after {ctx : Context T} (h : AsSoonAs ctx b J K) : After b J K :=
  after_iff.2 (h.tr_lt.trans_le J.fst_le_snd)

/-- *After* does not entail *as soon as*: unlike *as soon as*, it leaves open that the main clause
held before the reference point, as in *Ann felt happy after she wrote the article* (137). -/
theorem not_forall_after_imp_asSoonAs :
    ¬ ∀ (ctx : Context ℤ) (J K : NonemptyInterval ℤ),
      After .state J K → AsSoonAs ctx .state J K := by
  intro h
  have hA := (h ⟨0, 0, fun s t ↦ t < s, id⟩ ⟨(0, 2), by decide⟩ (pure 1)
    (after_iff.2 (by decide))).tr_lt
  exact absurd hA (by decide)

/-! ### Until and since -/

-- The final point of a subinterval of `J` can be any point of `J`.
theorem exists_le_snd_eq_iff {t : T} : (∃ J' ≤ J, J'.snd = t) ↔ t ∈ J :=
  ⟨fun ⟨J', hJ', ht⟩ ↦ ht ▸ ⟨(le_def.1 hJ').1.trans J'.fst_le_snd, (le_def.1 hJ').2⟩,
    fun ht ↦ ⟨pure t, le_def.2 ht, rfl⟩⟩

theorem Until.tr_mem {ctx : Context T} (h : Until ctx b J K) : tr b K ∈ J :=
  let ⟨_, J', hJ', ht, _⟩ := h
  exists_le_snd_eq_iff.1 ⟨J', hJ', ht⟩

-- (12) holds of a main clause that begins only at the reference point: `J'` may be a moment.
theorem until_of_fst_eq {ctx : Context T} (hJ : ¬ J.IsPoint) (h : J.fst = tr b K)
    (hctx : ctx.Outside J.fst (tr b K)) : Until ctx b J K :=
  ⟨hJ, pure J.fst, le_def.2 ⟨le_rfl, J.fst_le_snd⟩, h, hctx⟩

-- p. 141: *until* takes only main clauses that are not moments.
theorem not_until_of_isPoint {ctx : Context T} (hJ : J.IsPoint) : ¬ Until ctx b J K :=
  fun h ↦ h.1 hJ

-- (33), p. 141: *since* takes any main clause, as in *I have met an Eskimo since I came here*.
theorem exists_since_of_isPoint :
    ∃ (ctx : Context ℤ) (J K : NonemptyInterval ℤ), J.IsPoint ∧
      Since ctx .achievement .achievement False J K :=
  ⟨⟨3, 3, fun s t ↦ t < s, id⟩, pure 2, pure 1, rfl, ⟨(1, 3), by decide⟩,
    .inr (by decide), by simp [Durative], by simp, fun _ ↦ by decide, rfl, by decide⟩

theorem Holds.when_of_whenever {ctx : Context T} {A B : Clause T}
    (h : Holds ctx .whenever A B) (hB : B.intervals.Nonempty) : Holds ctx .when_ A B :=
  let ⟨K, hK⟩ := hB
  let ⟨J, hJ, hw⟩ := h K hK
  ⟨J, hJ, K, hK, hw⟩

end Preorder

section LinearOrder

variable {T : Type*} [LinearOrder T] {a b : VendlerClass} {J K : NonemptyInterval T}

/-! ### Converses and overlap -/

/-- *A before B* and *B after A* are converses exactly when `B` specifies a moment (p. 113). -/
theorem forall_before_iff_after_iff_isPoint :
    (∀ (a : VendlerClass) (J : NonemptyInterval T), Before a J K ↔ After a K J) ↔ K.IsPoint := by
  refine ⟨fun h ↦ ?_, fun hK a J ↦ ?_⟩
  · by_contra hK
    have hlt : K.fst < K.snd := K.fst_le_snd.lt_of_ne hK
    exact lt_irrefl _ <| (h .state (pure K.fst)).2 (after_iff.2 hlt)
  · rw [after_iff, Before, show K.fst = K.snd from hK]

-- Unless an accomplishment is involved, co-temporal intervals are overlapping ones.
theorem cotemporal_iff_overlaps (ha : a ≠ .accomplishment) (hb : b ≠ .accomplishment) :
    Cotemporal a b J K ↔ J.Overlaps K := by
  refine ⟨fun ⟨I, hJ, hK, _⟩ ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · have hJ := le_def.1 hJ
    have hK := le_def.1 hK
    exact ⟨hJ.1.trans (I.fst_le_snd.trans hK.2), hK.1.trans (I.fst_le_snd.trans hJ.2)⟩
  · exact ⟨⟨(max J.fst K.fst, min J.snd K.snd),
        max_le (le_min J.fst_le_snd h₁) (le_min h₂ K.fst_le_snd)⟩,
      le_def.2 ⟨le_max_left _ _, min_le_left _ _⟩, le_def.2 ⟨le_max_right _ _, min_le_right _ _⟩,
      (absurd · ha), (absurd · hb)⟩

/-- *While* does not entail *as long as*: two intervals may overlap with neither containing the
other. -/
theorem not_forall_while_imp_asLongAs :
    ¬ ∀ J K : NonemptyInterval ℤ, While .state .state J K → AsLongAs J K := by
  intro h
  have hw : While .state .state (⟨(0, 2), by decide⟩ : NonemptyInterval ℤ) ⟨(1, 3), by decide⟩ :=
    ⟨by decide, (cotemporal_iff_overlaps (by decide) (by decide)).2 (by decide)⟩
  exact absurd (h _ _ hw).2.2 (by decide)

-- (80) fails of an accomplishment *while*-clause and a moment.
theorem not_while_of_isPoint_of_accomplishment (hJ : J.IsPoint) (hK : ¬ K.IsPoint) :
    ¬ Cotemporal a .accomplishment J K := by
  rintro ⟨I, hIJ, _, _, hI⟩
  obtain rfl := hI rfl
  have h := le_def.1 hIJ
  exact hK <| le_antisymm K.fst_le_snd <| h.2.trans <| hJ.symm.le.trans h.1

/-! ### The judgments -/

/-- A pair of classes is admitted by a relation when some clauses of those classes satisfy its
truth conditions. -/
def Admits (T : Type*) [LinearOrder T] (r : Connective.Relation) (a b : VendlerClass) : Prop :=
  ∃ (ctx : Context T) (A B : Clause T), A.vendler = a ∧ B.vendler = b ∧ Holds ctx r A B

theorem not_isPoint_iff {A : Clause T} (hJ : J ∈ A.intervals) :
    ¬ J.IsPoint ↔ A.vendler.duration = .durative := by
  rw [A.isPoint_iff J hJ]
  cases A.vendler <;> decide

section Witness

variable {s t : T}

/-- The clause of class `c` specifying the interval `[s, t]` of an event that takes time, for
`s < t`. -/
private def Clause.long (hst : s < t) (c : VendlerClass) (hc : c.duration = .durative) :
    Clause T where
  vendler := c
  intervals := {⟨(s, t), hst.le⟩}
  isPoint_iff i hi := by
    obtain rfl := hi
    simp only [hc, reduceCtorEq, iff_false]
    exact hst.ne

/-- The clause of class `c` specifying the moment `s`. -/
private def Clause.moment (s : T) (c : VendlerClass) (hc : c.duration = .punctual) : Clause T where
  vendler := c
  intervals := {pure s}
  isPoint_iff i hi := by
    obtain rfl := hi
    simp only [hc, iff_true]
    rfl

/-- A context whose present moment and final point are `now`. -/
private def ctxAt (now : T) : Context T := ⟨now, now, fun s t ↦ t < s, id⟩

end Witness

private theorem duration_cases (c : VendlerClass) :
    c.duration = .durative ∨ c.duration = .punctual := by
  cases c <;> decide

variable (T) [Nontrivial T]

theorem admits_asLongAs_iff :
    Admits T .asLongAs a b ↔ a.duration = .durative ∧ b.duration = .durative := by
  constructor
  · rintro ⟨_, A, B, rfl, rfl, J, hJ, K, hK, h⟩
    exact ⟨(not_isPoint_iff hJ).1 h.1, (not_isPoint_iff hK).1 h.2.1⟩
  · rintro ⟨ha, hb⟩
    obtain ⟨s, t, hst⟩ := exists_pair_lt T
    exact ⟨ctxAt s, .long hst a ha, .long hst b hb, rfl, rfl, _, rfl, _, rfl,
      hst.ne, hst.ne, le_rfl⟩

theorem admits_while_iff :
    Admits T .while_ a b ↔
      b.duration = .durative ∧ ¬ (a.duration = .punctual ∧ b = .accomplishment) := by
  constructor
  · rintro ⟨_, A, B, rfl, rfl, J, hJ, K, hK, hK', hc⟩
    refine ⟨(not_isPoint_iff hK).1 hK', fun ⟨ha, hb⟩ ↦ ?_⟩
    rw [hb] at hc
    exact not_while_of_isPoint_of_accomplishment ((A.isPoint_iff J hJ).2 ha) hK' hc
  · rintro ⟨hb, hab⟩
    obtain ⟨s, t, hst⟩ := exists_pair_lt T
    rcases duration_cases a with ha | ha
    · exact ⟨ctxAt s, .long hst a ha, .long hst b hb, rfl, rfl, _, rfl, _, rfl, hst.ne,
        _, le_rfl, le_rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
    · have hbne : b ≠ .accomplishment := fun h ↦ hab ⟨ha, h⟩
      have hane : a ≠ .accomplishment := fun h ↦ by subst h; cases ha
      exact ⟨ctxAt s, .moment s a ha, .long hst b hb, rfl, rfl, _, rfl, _, rfl, hst.ne,
        pure s, le_rfl, le_def.2 ⟨le_rfl, hst.le⟩, (absurd · hane), (absurd · hbne)⟩

theorem admits_until_iff : Admits T .until_ a b ↔ a.duration = .durative := by
  constructor
  · rintro ⟨_, A, B, rfl, rfl, J, hJ, K, hK, h⟩
    exact (not_isPoint_iff hJ).1 h.1
  · intro ha
    obtain ⟨s, t, hst⟩ := exists_pair_lt T
    let J : NonemptyInterval T := ⟨(s, t), hst.le⟩
    rcases duration_cases b with hb | hb
    · -- The temporal clause takes time: an accomplishment's reference point is `t`, others' `s`.
      by_cases hacc : b = .accomplishment
      · subst hacc
        exact ⟨ctxAt s, .long hst a ha, .long hst _ hb, rfl, rfl, _, rfl, _, rfl, hst.ne,
          pure t, le_def.2 ⟨hst.le, le_rfl⟩, rfl, .inl hst⟩
      · have htr : tr b J = s := tr_of_ne hacc
        exact ⟨ctxAt t, .long hst a ha, .long hst b hb, rfl, rfl, _, rfl, _, rfl, hst.ne,
          pure s, le_def.2 ⟨le_rfl, hst.le⟩, htr.symm, .inr (htr.trans_lt hst)⟩
    · have hacc : b ≠ .accomplishment := fun h ↦ by subst h; cases hb
      have htr : tr b (pure s) = s := tr_of_ne hacc
      exact ⟨ctxAt t, .long hst a ha, .moment s b hb, rfl, rfl, _, rfl, _, rfl, hst.ne,
        pure s, le_def.2 ⟨le_rfl, hst.le⟩, htr.symm, .inr (htr.trans_lt hst)⟩

/-- The classes each of these connectives admits, by `admits_while_iff`, `admits_asLongAs_iff` and
`admits_until_iff`. -/
def Admitted : Connective.Relation → VendlerClass → VendlerClass → Prop
  | .while_, a, b => b.duration = .durative ∧ ¬ (a.duration = .punctual ∧ b = .accomplishment)
  | .asLongAs, a, b => a.duration = .durative ∧ b.duration = .durative
  | .until_, a, _ => a.duration = .durative
  | _, _, _ => True

instance : ∀ r a b, Decidable (Admitted r a b)
  | .while_, _, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .asLongAs, _, _ => inferInstanceAs (Decidable (_ ∧ _))
  | .until_, _, _ => inferInstanceAs (Decidable (_ = _))
  | .before, _, _ | .after, _, _ | .asSoonAs, _, _ | .when_, _, _ | .whenever, _, _
  | .since, _, _ => isTrue trivial

/-- The fragment's entries for the connectives of the rows. -/
def connectives : List (String × Connective) :=
  [ (English.TemporalConnectives.while_.form, English.TemporalConnectives.while_),
    (English.TemporalConnectives.asLongAs.form, English.TemporalConnectives.asLongAs),
    (English.TemporalConnectives.until_.form, English.TemporalConnectives.until_) ]

/-- The situation types the rows name. -/
def classes : List (String × VendlerClass) :=
  [("state", .state), ("activity", .activity), ("achievement", .achievement),
    ("accomplishment", .accomplishment)]

theorem admits_iff_admitted {r : Connective.Relation}
    (hr : r = .while_ ∨ r = .asLongAs ∨ r = .until_) : Admits T r a b ↔ Admitted r a b := by
  rcases hr with rfl | rfl | rfl
  · exact admits_while_iff T
  · exact admits_asLongAs_iff T
  · exact admits_until_iff T

theorem rows_admitted :
    ∀ r ∈ Examples.all, ∃ c ∈ r.parse? "connective" connectives,
      (c.relation = .while_ ∨ c.relation = .asLongAs ∨ c.relation = .until_) ∧
      ∃ a ∈ r.parse? "main" classes, ∃ b ∈ r.parse? "temporal" classes,
        (a = .accomplishment ∧ c.relation ≠ .while_) ∨
          (r.judgment = .acceptable ↔ Admitted c.relation a b) := by
  decide

/-- The formulas of *while*, *as long as* and *until* give every judgment of the paper's rows, but
for the accomplishment main clauses of *as long as* and *until*. -/
theorem rows_predicted :
    ∀ r ∈ Examples.all, ∃ c ∈ r.parse? "connective" connectives,
      ∃ a ∈ r.parse? "main" classes, ∃ b ∈ r.parse? "temporal" classes,
        (a = .accomplishment ∧ c.relation ≠ .while_) ∨
          (r.judgment = .acceptable ↔ Admits T c.relation a b) := fun r hr ↦
  let ⟨c, hc, hrel, a, ha, b, hb, h⟩ := rows_admitted r hr
  ⟨c, hc, a, ha, b, hb, h.imp_right (·.trans (admits_iff_admitted T hrel).symm)⟩

/-- (12) and (93) admit the accomplishment main clauses of (5) and (88), against the judgments. -/
theorem rows_accomplishment_admitted :
    (Admits T .asLongAs .accomplishment .state ∧ Examples.ex_88.judgment ≠ .acceptable) ∧
      Admits T .until_ .accomplishment .achievement ∧ Examples.ex_5.judgment ≠ .acceptable :=
  ⟨⟨(admits_asLongAs_iff T).2 (by decide), by decide⟩,
    (admits_until_iff T).2 (by decide), by decide⟩

end LinearOrder

end Heinamaki1974
