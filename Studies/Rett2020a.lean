module

public import Studies.BeaverCondoravdi2003
public import Linglib.Semantics.Degree.Comparison
public import Linglib.Data.Examples.Rett2020a
public import Linglib.Data.Examples.Readers

/-!
# Rett (2020): Eliminating EARLIEST: a general semantics for before and after

This file formalizes the paper's semantics for *before* and *after* as antonyms over converse
scales. Each relates some time of its main clause to the most informative time of its embedded
clause, the least on the *before* scale and the greatest on the *after* scale, `before` and
`after`, with maximality relativized to the scale as in the degree domain,
`Degree.maxOnScale`. Two aspectual coercions supply the remaining readings: a process may
denote the onset of its duration, `inchoative`, and a culmination its telos, `completive`, so
that against a process an *after* clause is ambiguous between the end and the onset while a
*before* clause is not, and against a culmination a *before* clause is ambiguous between the
start and the telos while an *after* clause is not: the six readings of the paper's Table 1
and no seventh, `before_process`, `before_culmination_telos`, `after_process_onset`,
`after_culmination`, instantiated by the paper's (23) and (24). The default readings are
downward entailing in the embedded clause, `before_antitone` and `after_antitone`, the
account's route to NPI licensing, and the coerced readings are not,
`not_before_completive_antitone`. Anscombe's *before*, a time of the main clause before every
time of the embedded clause, is the default reading whenever the embedded clause has a first
time, `before_iff_beforeEver`.

*After* is *before* on the reversed time line, `after_iff_before_dual`, so the two share whatever
order reversal preserves: `after_antitone` follows from `before_antitone`, and both are
veridical, `nonempty_of_before` and `nonempty_of_after`. *Before* is Beaver and Condoravdi's
uniform *before*, `before_iff_uniform`, and so agrees with *before ever* on a clause exactly when
the clause has a first time or no time precedes all of it, `forall_before_iff_beforeEver`, while
*after* agrees with Anscombe's exactly on an instantaneous clause, `forall_after_iff_after`.

## Implementation notes

Run times are sets of intervals, and an eventuality's duration is its `timeTrace`; the
coercions act on the trace, so an eventuality's class enters only through which coercion
`readings` makes available, as in the paper's (19) and (21). Of the typological
survey of section 2.4, the rows record the Serbo-Croatian and Tagalog sentences whose overt aspect
selects a reading, `Marking.select`, with the unambiguous Tagalog *before* and German *after*
sentences. The paper takes the veridicality asymmetry from Condoravdi's branching time
(§3.3.2), which this file does not formalize, and NPI licensing from the monotonicity of the
default readings.

## References

* [J. Rett, *Eliminating EARLIEST: a general semantics for before and after*
  (2020)][rett-2020a]
* [G. E. M. Anscombe, *Before and after* (1964)][anscombe-1964]
* [O. Heinämäki, *Semantics of English temporal connectives* (1974)][heinamaki-1974]
* [D. Beaver, C. Condoravdi, *A uniform analysis of before and after*
  (2003)][beaver-condoravdi-2003]
* [C. Condoravdi, *NPI licensing in temporal clauses* (2010)][condoravdi-2010]
* [M. Krifka, *Before and after without coercion: comment on the paper by Cleo Condoravdi*
  (2010)][krifka-2010b]
* [H. de Swart, *Aspect shift and coercion* (1998)][de-swart-1998]
* [J. Dölling, *Aspectual coercion and eventuality structure* (2014)][dolling-2014]
* [H. Rullmann, *Maximality in the semantics of wh-constructions* (1995)][rullmann-1995]
* [C. Kennedy, *Projecting the adjective* (1997)][kennedy-1997]
-/

@[expose] public section

namespace Rett2020a

open Tense Degree Anscombe1964

variable {T : Type*} [LinearOrder T]

/-! ### The relations and the coercions -/

/-- *A before B* (22a) holds when some time of `A` precedes the most informative time of `B` on the
*before* scale, its least. -/
def before (A B : Set (NonemptyInterval T)) : Prop :=
  ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale .lt (timeTrace B), t < m

/-- *A after B* (22b) holds when some time of `A` follows the most informative time of `B` on the
*after* scale, its greatest. -/
def after (A B : Set (NonemptyInterval T)) : Prop :=
  ∃ t ∈ timeTrace A, ∃ m ∈ maxOnScale .gt (timeTrace B), m < t

/-- Under inchoative coercion (19) a process may denote the onset of its duration, the greatest
lower bound of its times. -/
def inchoative (p : Set (NonemptyInterval T)) : Set (NonemptyInterval T) :=
  {i | ∃ g, IsLeast (timeTrace p) g ∧ i = NonemptyInterval.pure g}

/-- Under completive coercion (21) a culmination may denote its telos, the least upper bound of its
times. -/
def completive (p : Set (NonemptyInterval T)) : Set (NonemptyInterval T) :=
  {i | ∃ l, IsGreatest (timeTrace p) l ∧ i = NonemptyInterval.pure l}

/-- The paper groups the aspectual classes of Moens and Steedman into processes, states and
activities, and culminations, accomplishments and achievements. -/
inductive Class where
  | process
  | culmination

/-- An embedded eventuality of a class with run times `p` may denote the run times themselves or the
coercion its class allows. -/
def readings : Class → Set (NonemptyInterval T) → Set (Set (NonemptyInterval T))
  | .process, p => {p, inchoative p}
  | .culmination, p => {p, completive p}

theorem timeTrace_inchoative (p : Set (NonemptyInterval T)) :
    timeTrace (inchoative p) = {g | IsLeast (timeTrace p) g} := by
  ext t
  simp only [mem_timeTrace, inchoative, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, ht⟩
    exact (NonemptyInterval.mem_pure.mp ht) ▸ hg
  · exact fun h ↦ ⟨_, ⟨t, h, rfl⟩, NonemptyInterval.mem_pure.mpr rfl⟩

theorem timeTrace_completive (p : Set (NonemptyInterval T)) :
    timeTrace (completive p) = {l | IsGreatest (timeTrace p) l} := by
  ext t
  simp only [mem_timeTrace, completive, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨l, hl, rfl⟩, ht⟩
    exact (NonemptyInterval.mem_pure.mp ht) ▸ hl
  · exact fun h ↦ ⟨_, ⟨t, h, rfl⟩, NonemptyInterval.mem_pure.mpr rfl⟩

variable {A B : Set (NonemptyInterval T)} {m : T}

theorem before_iff_of_isLeast (h : IsLeast (timeTrace B) m) :
    before A B ↔ ∃ t ∈ timeTrace A, t < m := by
  simp only [before, maxOnScale_lt_eq, Set.mem_ofPred_eq]
  exact ⟨fun ⟨t, ht, _, hm, htm⟩ ↦ ⟨t, ht, hm.unique h ▸ htm⟩,
    fun ⟨t, ht, htm⟩ ↦ ⟨t, ht, m, h, htm⟩⟩

theorem after_iff_of_isGreatest (h : IsGreatest (timeTrace B) m) :
    after A B ↔ ∃ t ∈ timeTrace A, m < t := by
  simp only [after, maxOnScale_gt_eq, Set.mem_ofPred_eq]
  exact ⟨fun ⟨t, ht, _, hm, htm⟩ ↦ ⟨t, ht, hm.unique h ▸ htm⟩,
    fun ⟨t, ht, htm⟩ ↦ ⟨t, ht, m, h, htm⟩⟩

theorem timeTrace_completive_of_isGreatest (h : IsGreatest (timeTrace B) m) :
    timeTrace (completive B) = {m} := by
  rw [timeTrace_completive]
  exact Set.eq_singleton_iff_unique_mem.mpr ⟨h, fun _ hx ↦ hx.unique h⟩

theorem timeTrace_inchoative_of_isLeast (h : IsLeast (timeTrace B) m) :
    timeTrace (inchoative B) = {m} := by
  rw [timeTrace_inchoative]
  exact Set.eq_singleton_iff_unique_mem.mpr ⟨h, fun _ hx ↦ hx.unique h⟩

theorem before_completive_iff (h : IsGreatest (timeTrace B) m) :
    before A (completive B) ↔ ∃ t ∈ timeTrace A, t < m :=
  before_iff_of_isLeast (by rw [timeTrace_completive_of_isGreatest h]; exact isLeast_singleton)

theorem after_inchoative_iff (h : IsLeast (timeTrace B) m) :
    after A (inchoative B) ↔ ∃ t ∈ timeTrace A, m < t :=
  after_iff_of_isGreatest (by rw [timeTrace_inchoative_of_isLeast h]; exact isGreatest_singleton)

theorem before_inchoative_iff (h : IsLeast (timeTrace B) m) :
    before A (inchoative B) ↔ before A B := by
  rw [before_iff_of_isLeast h, before_iff_of_isLeast (B := inchoative B)]
  rw [timeTrace_inchoative_of_isLeast h]; exact isLeast_singleton

theorem after_completive_iff (h : IsGreatest (timeTrace B) m) :
    after A (completive B) ↔ after A B := by
  rw [after_iff_of_isGreatest h, after_iff_of_isGreatest (B := completive B)]
  rw [timeTrace_completive_of_isGreatest h]; exact isGreatest_singleton

/-! ### Table 1 -/

variable (A) (i : NonemptyInterval T)

/-- Against a process, *before* has one reading, precedence of its onset ((4a)), since inchoative
coercion changes nothing and completive coercion is unavailable. -/
theorem before_process :
    ∀ B ∈ readings .process (Set.Iic i), (before A B ↔ ∃ t ∈ timeTrace A, t < i.fst) := by
  simp only [readings, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨before_iff_of_isLeast (isLeast_timeTrace_Iic i),
    (before_inchoative_iff (isLeast_timeTrace_Iic i)).trans
      (before_iff_of_isLeast (isLeast_timeTrace_Iic i))⟩

-- (5a), (23a)
theorem before_culmination_start :
    before A {i} ↔ ∃ t ∈ timeTrace A, t < i.fst :=
  before_iff_of_isLeast (isLeast_timeTrace_singleton i)

/-- ... or, under completive coercion, of its telos ((23b)). -/
theorem before_culmination_telos :
    before A (completive {i}) ↔ ∃ t ∈ timeTrace A, t < i.snd :=
  before_completive_iff (isGreatest_timeTrace_singleton i)

-- (5b), (24a)
theorem after_process_end :
    after A (Set.Iic i) ↔ ∃ t ∈ timeTrace A, i.snd < t :=
  after_iff_of_isGreatest (isGreatest_timeTrace_Iic i)

/-- ... or, under inchoative coercion, of its onset ((24b)). -/
theorem after_process_onset :
    after A (inchoative (Set.Iic i)) ↔ ∃ t ∈ timeTrace A, i.fst < t :=
  after_inchoative_iff (isLeast_timeTrace_Iic i)

/-- Against a culmination, *after* has one reading, succession of its telos ((4b)), since completive
coercion changes nothing and inchoative coercion is unavailable. -/
theorem after_culmination :
    ∀ B ∈ readings .culmination {i},
      (after A B ↔ ∃ t ∈ timeTrace A, i.snd < t) := by
  simp only [readings, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact ⟨after_iff_of_isGreatest (isGreatest_timeTrace_singleton i),
    (after_completive_iff (isGreatest_timeTrace_singleton i)).trans
      (after_iff_of_isGreatest (isGreatest_timeTrace_singleton i))⟩

theorem before_stative_iff (h : IsLeast (timeTrace B) m) :
    before (Set.Iic i) B ↔ i.fst < m := by
  rw [before_iff_of_isLeast h]
  exact ⟨fun ⟨_, ht, htm⟩ ↦ (mem_timeTrace_Iic.mp ht).1.trans_lt htm,
    fun h ↦ ⟨i.fst, (isLeast_timeTrace_Iic i).1, h⟩⟩

theorem after_stative_iff (h : IsGreatest (timeTrace B) m) :
    after (Set.Iic i) B ↔ m < i.snd := by
  rw [after_iff_of_isGreatest h]
  exact ⟨fun ⟨_, ht, htm⟩ ↦ htm.trans_le (mem_timeTrace_Iic.mp ht).2,
    fun h ↦ ⟨i.snd, (isGreatest_timeTrace_Iic i).1, h⟩⟩

variable (j : NonemptyInterval T)

theorem before_stative_accomplishment_iff :
    before (Set.Iic i) {j} ↔ i.fst < j.fst :=
  before_stative_iff i (isLeast_timeTrace_singleton j)

theorem before_stative_completive_iff :
    before (Set.Iic i) (completive {j}) ↔ i.fst < j.snd :=
  before_stative_iff i (by
    rw [timeTrace_completive_of_isGreatest (isGreatest_timeTrace_singleton j)]
    exact isLeast_singleton)

theorem after_stative_stative_iff :
    after (Set.Iic i) (Set.Iic j) ↔ j.snd < i.snd :=
  after_stative_iff i (isGreatest_timeTrace_Iic j)

theorem after_stative_inchoative_iff :
    after (Set.Iic i) (inchoative (Set.Iic j)) ↔ j.fst < i.snd :=
  after_stative_iff i (by
    rw [timeTrace_inchoative_of_isLeast (isLeast_timeTrace_Iic j)]
    exact isGreatest_singleton)

-- (23)
theorem example23 :
    ¬ before {NonemptyInterval.pure 15} {⟨⟨13, 16⟩, by omega⟩} ∧
      before {NonemptyInterval.pure 15}
        (completive {⟨⟨13, 16⟩, by omega⟩}) := by
  simp [before_culmination_start, before_culmination_telos]

-- (24)
theorem example24 :
    ¬ after {NonemptyInterval.pure 2022} (Set.Iic ⟨⟨2021, 2028⟩, by omega⟩) ∧
      after {NonemptyInterval.pure 2022}
        (inchoative (Set.Iic ⟨⟨2021, 2028⟩, by omega⟩)) := by
  simp [after_process_end, after_process_onset]

/-! ### Antonymy as order duality

On the reversed time line the *after* scale is the *before* scale, so *after* is *before* there.
Whatever order reversal preserves *before* and *after* then share, among it monotonicity in the
embedded clause and veridicality, so the asymmetries between them cannot come from the
connectives. The paper derives veridicality from branching time instead (§3.3.2). -/

section Duality

variable {A}

private theorem timeTrace_image_dual (A : Set (NonemptyInterval T)) :
    timeTrace (NonemptyInterval.dual '' A) = OrderDual.ofDual ⁻¹' timeTrace A := by
  ext t
  simp only [mem_timeTrace, Set.mem_image, exists_exists_and_eq_and, Set.mem_preimage,
    NonemptyInterval.mem_def, NonemptyInterval.fst_dual, NonemptyInterval.snd_dual,
    OrderDual.toDual_le, OrderDual.le_toDual]
  exact exists_congr fun _ ↦ and_congr_right fun _ ↦ and_comm

theorem after_iff_before_dual :
    after A B ↔ before (NonemptyInterval.dual '' A) (NonemptyInterval.dual '' B) := by
  simp only [after, before, timeTrace_image_dual, maxOnScale_lt_eq, maxOnScale_gt_eq]
  exact Iff.rfl

theorem nonempty_of_before : before A B → (timeTrace B).Nonempty := by
  rintro ⟨-, -, m, hm, -⟩
  rw [maxOnScale_lt_eq, Set.mem_ofPred_eq] at hm
  exact ⟨m, hm.1⟩

theorem nonempty_of_after (h : after A B) : (timeTrace B).Nonempty := by
  obtain ⟨t, ht⟩ := nonempty_of_before (after_iff_before_dual.1 h)
  rw [timeTrace_image_dual] at ht
  exact ⟨_, ht⟩

end Duality

/-! ### Monotonicity -/

theorem before_antitone {B' : Set (NonemptyInterval T)} (h : timeTrace B' ⊆ timeTrace B)
    (hB' : ∃ m', IsLeast (timeTrace B') m') : before A B → before A B' := by
  rintro ⟨t, ht, m, hm, htm⟩
  obtain ⟨m', hm'⟩ := hB'
  rw [maxOnScale_lt_eq] at hm
  exact ⟨t, ht, m', by rw [maxOnScale_lt_eq]; exact hm', htm.trans_le (hm.2 (h hm'.1))⟩

theorem after_antitone {B' : Set (NonemptyInterval T)} (h : timeTrace B' ⊆ timeTrace B)
    (hB' : ∃ m', IsGreatest (timeTrace B') m') : after A B → after A B' := by
  obtain ⟨m', hm'⟩ := hB'
  simp only [after_iff_before_dual]
  exact before_antitone _ (by simpa only [timeTrace_image_dual] using Set.preimage_mono h)
    ⟨OrderDual.toDual m', by simpa only [timeTrace_image_dual] using hm'.dual⟩

/-- The coerced reading of *before* is not downward entailing, so a *before* clause licenses NPIs
only on its default reading (25). -/
theorem not_before_completive_antitone (h₃ : ∃ a b c : T, a < b ∧ b < c) :
    ¬ ∀ A B B' : Set (NonemptyInterval T), timeTrace B' ⊆ timeTrace B →
      (∃ l', IsGreatest (timeTrace B') l') →
        before A (completive B) → before A (completive B') := by
  obtain ⟨a, b, c, hab, hbc⟩ := h₃
  intro h
  have := h {NonemptyInterval.pure b} {⟨⟨a, c⟩, hab.le.trans hbc.le⟩}
    {NonemptyInterval.pure a}
    (by
      rw [timeTrace_singleton, timeTrace_singleton]
      rintro t ht
      obtain rfl := NonemptyInterval.mem_pure.mp ht
      exact NonemptyInterval.mem_def.mpr ⟨le_rfl, hab.le.trans hbc.le⟩)
    ⟨a, isGreatest_timeTrace_singleton _⟩
    ((before_culmination_telos _ _).mpr ⟨b, mem_timeTrace_pure.mpr rfl, hbc⟩)
  obtain ⟨t, ht, htm⟩ := (before_culmination_telos _ _).mp this
  obtain rfl := mem_timeTrace_pure.mp ht
  exact absurd (htm.trans hab) (lt_irrefl _)

/-! ### Anscombe -/

theorem before_iff_beforeEver (h : IsLeast (timeTrace B) m) :
    before A B ↔ Tense.beforeEver A B :=
  (before_iff_of_isLeast h).trans (beforeEver_iff_of_isLeast h).symm

theorem after_imp_after : after A B → Anscombe.after A B := by
  rintro ⟨t, ht, m, hm, htm⟩
  exact ⟨t, ht, m, hm.1, htm⟩

section Divergence

variable {A}

theorem forall_after_iff_after (hB : IsGreatest (timeTrace B) m) :
    (∀ A, after A B ↔ Anscombe.after A B) ↔ Instantaneous B := by
  refine ⟨fun h ↦ ⟨m, Set.eq_singleton_iff_unique_mem.2 ⟨hB.1, fun t ht ↦ ?_⟩⟩, fun ⟨t, ht⟩ A ↦ ?_⟩
  · refine (hB.2 ht).eq_of_not_lt fun hlt ↦ ?_
    obtain ⟨_, hs, m', hm', hlt'⟩ := (h {NonemptyInterval.pure m}).2 ⟨m, by simp, t, ht, hlt⟩
    rw [maxOnScale_gt_eq, Set.mem_ofPred_eq] at hm'
    rw [mem_timeTrace_pure.1 hs, hm'.unique hB] at hlt'
    exact lt_irrefl m hlt'
  · rw [after_iff_of_isGreatest (by rw [ht]; exact isGreatest_singleton),
      after_iff_least_lt (by rw [ht]; exact isLeast_singleton)]

/-! ### Beaver and Condoravdi -/

theorem before_iff_uniform :
    before A B ↔ BeaverCondoravdi2003.uniform (· < ·) (timeTrace A) (timeTrace B) := by
  simp only [before, BeaverCondoravdi2003.uniform, maxOnScale_lt_eq, Set.mem_ofPred_eq]

/-- *Before* agrees with Anscombe's *before ever* on a clause iff the clause has a first time or no
time precedes all of it (Proposition 2 of Beaver and Condoravdi). -/
theorem forall_before_iff_beforeEver :
    (∀ A, before A B ↔ beforeEver A B) ↔
      (∃ m, IsLeast (timeTrace B) m) ∨ strictLowerBounds (timeTrace B) = ∅ := by
  simpa only [before_iff_uniform] using BeaverCondoravdi2003.forall_uniform_lt_iff_beforeEver

end Divergence

/-! ### Overt aspect marking -/

/-- In a language that grammaticizes the coercion, the aspect of an embedded culmination decides it.
The Serbo-Croatian perfective and the Tagalog ability-and-involuntary-action perfective are
culminating, and their imperfective and neutral-perfective counterparts non-culminating, (11) and
(12). -/
inductive Marking
  | nonCulminating
  | culminating
  deriving DecidableEq

/-- A marking selects a culmination's run times, or under a culminating marking their telos. -/
def Marking.select : Marking → Set (NonemptyInterval T) → Set (NonemptyInterval T)
  | .nonCulminating, p => p
  | .culminating, p => completive p

theorem Marking.select_mem_readings (m : Marking) (p : Set (NonemptyInterval T)) :
    m.select p ∈ readings .culmination p := by
  cases m <;> simp [Marking.select, readings]

/-- The bound of the embedded eventuality a *before* clause is read against. -/
inductive Bound
  | initial
  | final
  deriving DecidableEq

/-- The time of a bound of an interval. -/
def Bound.time : Bound → NonemptyInterval T → T
  | .initial, i => i.fst
  | .final, i => i.snd

/-- A non-culminating marking reads *before* against the onset, a culminating one against the
telos. -/
def Marking.bound : Marking → Bound
  | .nonCulminating => .initial
  | .culminating => .final

theorem before_select (m : Marking) :
    before A (m.select {i}) ↔ ∃ t ∈ timeTrace A, t < m.bound.time i := by
  cases m
  · exact before_culmination_start A i
  · exact before_culmination_telos A i

/-- The marking of a row's embedded clause. -/
def marking? (r : Datum) : Option Marking :=
  r.parse? "aspect" [("imperfective", .nonCulminating), ("perfective", .culminating),
    ("pfv.neut", .nonCulminating), ("aia", .culminating)]

/-- The bounds a row's accepted readings are read against. -/
def bounds (r : Datum) : List Bound :=
  (r.readings.filter (·.2 = .acceptable)).filterMap fun x ↦
    match x.1 with
    | "before-start" => some .initial
    | "before-finish" => some .final
    | _ => none

theorem rows_marking : ∀ r ∈ Examples.all, ∀ m ∈ marking? r, bounds r = [m.bound] := by
  decide

end Rett2020a
