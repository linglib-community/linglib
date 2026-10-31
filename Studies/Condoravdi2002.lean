module

public import Mathlib.Tactic.DeriveFintype
public import Linglib.Data.Examples.Condoravdi2002
public import Linglib.Semantics.Aspect.Instantiation
public import Linglib.Semantics.Modality.HistoricalAlternatives
public import Linglib.Semantics.Modality.Basic
public import Linglib.Data.Examples.Readers

/-!
# Condoravdi 2002: Temporal Interpretation of Modals

Non-root modals expand the time of evaluation forward and instantiate the property in their
scope in the worlds of a modal base. Modals for the past are the same modals over the perfect,
so *might have* is ambiguous between the modal over the perfect, an epistemic possibility about
the past, and the perfect over the modal, a metaphysical possibility from a past perspective.
Frame adverbials follow from intersecting the reference interval with the period named, *still*
and *already* over a modal from the shrinking of live options as time advances, and the choice
of modal base from the diversity condition, which a settled issue fails. The operators are
stated over closed intervals of times that may run to the end of time.

## Implementation notes

* The paper's *now* is an interval, albeit a short one, taken here as a point, and a modal base
  is indexed by the start of the reference interval; the paper's `MB(w, t)` takes an interval
  and its `w ≃_t w'` a point.
* Identity of the past enters as `FixesPast`, discharged for histories built from dated facts
  by `fixesPast_eventive` and `fixesPast_stative`; the counterfactual implication rests on
  the paper's footnote assumption `PastAlternativesOutside`.
* The sortal restriction of *already*, *yet* and *still* is partiality, and only the
  prior-phase half of their Löbner presuppositions is stated.

## TODO

* The embedded modals of *Mary believed that John may get sick* are informal in the paper and
  absent here.
* *He has still won* is excluded by the paper as well known rather than derived; the German
  *noch* pattern that rests on it is a row, not a theorem.

## References

* [C. Condoravdi, *Temporal Interpretation of Modals* (2002)][condoravdi-2002]
* [F. Mondadori, *Remarks on Tense and Mood: The Perfect Future* (1978)][mondadori-1978]
* [D. Abusch, *Sequence of Tense and Temporal De Re* (1997)][abusch-1997]
* [D. Abusch, *Generalizing Tense Semantics for Future Contexts* (1998)][abusch-1998]
* [M. Enç, *Tense and Modality* (1996)][enc-1996]
* [J. Groenendijk and M. Stokhof, *Modality and Conversational Information*
  (1975)][groenendijk-stokhof-1975]
* [A. Kratzer, *The Notional Category of Modality* (1981)][kratzer-1981]
* [D. Lewis, *Counterfactual Dependence and Time's Arrow* (1979)][lewis-1979-time-arrow]
* [S. Löbner, *German schon, erst, noch: An Integrated Analysis* (1989)][lobner-1989]
* [R. Thomason, *Combinations of Tense and Modality* (1984)][thomason-1984]
-/

@[expose] public section

namespace Condoravdi2002

open Event (τ)

open Aspect HistoricalAlternatives
open Modality (TemporalPerspective TemporalOrientation)

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] {P : W → E → Prop}
  {Q Q' : SortedProperty W E T}
  {r : Interval (WithTop T)} {t t' : T} {w : W}

/-! ### The operators -/

/-- The present tense instantiates the property at the time of utterance. -/
def PRES (now : T) (Q : SortedProperty W E T) (w : W) : Prop := At (Interval.pure ↑now) w Q

/-- The perfect instantiates the property at some interval preceding the reference interval. -/
def PERF (Q : SortedProperty W E T) : SortedProperty W E T :=
  .temporal fun w t ↦ ∃ t' : NonemptyInterval (WithTop T), Interval.Precedes ↑t' t ∧ At ↑t' w Q

/-- MAY and MIGHT instantiate the property in some world of the modal base at the start of the
reference interval, throughout the interval expanded forward to the end of time. -/
def MAY (MB : W → T → Set W) (Q : SortedProperty W E T) : SortedProperty W E T :=
  .temporal fun w t ↦ ∃ t₀ : T, IsLeast (t : Set (WithTop T)) ↑t₀ ∧
    ∃ w' ∈ MB w t₀, At (Interval.Ici ↑t₀) w' Q

/-- WOLL, the untensed modal of *will* and *would*, instantiates the property in every world of the
modal base at the start of the reference interval, throughout the forward interval. -/
def WOLL (MB : W → T → Set W) (Q : SortedProperty W E T) : SortedProperty W E T :=
  .temporal fun w t ↦ ∃ t₀ : T, IsLeast (t : Set (WithTop T)) ↑t₀ ∧
    ∀ w' ∈ MB w t₀, At (Interval.Ici ↑t₀) w' Q

/-- A frame adverbial such as *yesterday* instantiates a property of eventualities within
the intersection of the reference interval with the period named. The paper leaves it undefined
on properties of times, which the theorems carry as `IsEventuality`. -/
def frame (period : Interval (WithTop T)) (Q : SortedProperty W E T) : SortedProperty W E T :=
  .temporal fun w t ↦ At (t ⊓ period) w Q

/-- *Already*, *yet* and *still* are the identity on properties of states and of times and undefined
on properties of events. -/
def phase : SortedProperty W E T → Option (SortedProperty W E T)
  | .eventive _ => none
  | Q => some Q

/-! ### Characterizations -/

variable {MB : W → T → Set W} {now : T}

theorem at_coe_may_iff {i : NonemptyInterval (WithTop T)} :
    At ↑i w (MAY MB Q) ↔ ∃ t₀ : T, i.fst = ↑t₀ ∧ ∃ w' ∈ MB w t₀, At (Interval.Ici ↑t₀) w' Q :=
  exists_congr fun _ ↦ and_congr_left fun _ ↦
    ⟨fun h ↦ (h.unique Interval.isLeast_coe_fst).symm, fun h ↦ h ▸ Interval.isLeast_coe_fst⟩

@[simp] theorem pres_may_iff :
    PRES now (MAY MB Q) w ↔ ∃ w' ∈ MB w now, At (Interval.Ici ↑now) w' Q := by
  rw [PRES, Interval.pure, at_coe_may_iff]
  constructor
  · rintro ⟨t₀, ht₀, h⟩
    obtain rfl : t₀ = now := (WithTop.coe_eq_coe.1 ht₀).symm
    exact h
  · exact fun h ↦ ⟨now, rfl, h⟩

@[simp] theorem pres_woll_iff :
    PRES now (WOLL MB Q) w ↔ ∀ w' ∈ MB w now, At (Interval.Ici ↑now) w' Q := by
  rw [PRES, Interval.pure]
  refine ⟨fun ⟨t₀, ht₀, h⟩ ↦ ?_, fun h ↦ ⟨now, Interval.isLeast_coe_fst, h⟩⟩
  obtain rfl : t₀ = now := WithTop.coe_eq_coe.1 (ht₀.unique Interval.isLeast_coe_fst)
  exact h

@[simp] theorem at_Ici_perf_eventive_iff {t : T} :
    At (Interval.Ici ↑t) w (PERF (.eventive P)) ↔ ∃ e, P w e ∧ (τ e).snd < t := by
  constructor
  · rintro ⟨t', ht', e, he, hle⟩
    exact ⟨e, he, WithTop.coe_lt_coe.1
      (ht' (Interval.coe_le_iff.1 hle).2 (Interval.mem_Ici.2 le_rfl))⟩
  · rintro ⟨e, he, h⟩
    exact ⟨(τ e).withTop, Interval.precedes_withTop_Ici.2 h, e, he, le_rfl⟩

@[simp] theorem pres_perf_may_iff :
    PRES now (PERF (MAY MB Q)) w ↔ ∃ t' < now, ∃ w' ∈ MB w t', At (Interval.Ici ↑t') w' Q := by
  constructor
  · rintro ⟨i, hi, hat⟩
    obtain ⟨t', hfst, w', hw', h⟩ := at_coe_may_iff.1 hat
    refine ⟨t', WithTop.coe_lt_coe.1 (hi ?_ (Interval.mem_pure.2 rfl)), w', hw', h⟩
    exact hfst ▸ Interval.isLeast_coe_fst.1
  · rintro ⟨t', ht', w', hw', h⟩
    exact ⟨(NonemptyInterval.pure t').withTop, Interval.precedes_withTop_pure.2 ht',
      at_coe_may_iff.2 ⟨t', rfl, w', hw', h⟩⟩

/-! ### The three readings -/

theorem pres_may_eventive_iff :
    PRES now (MAY MB (.eventive P)) w ↔ ∃ w' ∈ MB w now, ∃ e, P w' e ∧ now ≤ (τ e).fst := by
  simp

theorem pres_may_stative_iff :
    PRES now (MAY MB (.stative P)) w ↔ ∃ w' ∈ MB w now, ∃ e, P w' e ∧ now ≤ (τ e).snd := by
  simp

theorem pres_may_perf_eventive_iff :
    PRES now (MAY MB (PERF (.eventive P))) w ↔
      ∃ w' ∈ MB w now, ∃ e, P w' e ∧ (τ e).snd < now := by
  simp

theorem pres_perf_may_eventive_iff :
    PRES now (PERF (MAY MB (.eventive P))) w ↔
      ∃ t' < now, ∃ w' ∈ MB w t', ∃ e, P w' e ∧ t' ≤ (τ e).fst := by
  simp

/-! ### Frame adverbials -/

theorem frame_modal_past (hQ : Q.IsEventuality) {period : Interval (WithTop T)}
    (hp : period.Precedes (Interval.Ici ↑now)) : ¬ PRES now (MAY MB (frame period Q)) w := by
  simp only [pres_may_iff]
  rintro ⟨w', -, h⟩
  obtain ⟨x, hx⟩ := exists_mem_of_at hQ h
  simp only [Interval.mem_inf] at hx
  exact lt_irrefl _ (hp hx.2 hx.1)

theorem frame_modalPerf_nonpast (hQ : Q.IsEventuality) {period : Interval (WithTop T)}
    (hp : period ≤ Interval.Ici ↑now) : ¬ PRES now (MAY MB (PERF (frame period Q))) w := by
  simp only [pres_may_iff]
  rintro ⟨w', -, t', ht', h⟩
  obtain ⟨x, hx⟩ := exists_mem_of_at hQ h
  simp only [Interval.mem_inf] at hx
  exact lt_irrefl _
    (lt_of_lt_of_le (ht' hx.1 (Interval.mem_Ici.2 le_rfl)) (Interval.le_Ici_iff.1 hp _ hx.2))

/-! ### Live options shrink -/

theorem may_antitone {history : HistoricalAlternatives W T}
    (hBC : ∀ w, Antitone (metaphysicalBase history w)) (hQ : Q.IsEventuality) :
    Antitone fun t : T ↦ PRES t (MAY (metaphysicalBase history) Q) w := by
  simp only [pres_may_iff]
  rintro t' t h ⟨w', hw', hat⟩
  exact ⟨w', hBC w h hw', hat.mono hQ (Interval.antitone_Ici (WithTop.coe_le_coe.2 h))⟩

/-- The prior-phase half of Löbner's presupposition of *already* requires a prior negative phase. -/
def AlreadyPresup (Q : SortedProperty W E T) (w : W) (now : T) : Prop := ∃ t' < now, ¬ PRES t' Q w

/-- The prior-phase half of Löbner's presupposition of *still* requires a prior positive phase. -/
def StillPresup (Q : SortedProperty W E T) (w : W) (now : T) : Prop := ∃ t' < now, PRES t' Q w

theorem not_already_may {history : HistoricalAlternatives W T}
    (hBC : ∀ w, Antitone (metaphysicalBase history w)) (hQ : Q.IsEventuality)
    (h : PRES now (MAY (metaphysicalBase history) Q) w) :
    ¬ AlreadyPresup (MAY (metaphysicalBase history) Q) w now :=
  fun ⟨_, ht', hn⟩ ↦ hn (may_antitone hBC hQ ht'.le h)

theorem still_may {history : HistoricalAlternatives W T}
    (hBC : ∀ w, Antitone (metaphysicalBase history w)) (hQ : Q.IsEventuality)
    (h : PRES now (MAY (metaphysicalBase history) Q) w) (ht' : t' < now) :
    StillPresup (MAY (metaphysicalBase history) Q) w now :=
  ⟨t', ht', may_antitone hBC hQ ht'.le h⟩

/-! ### Settledness and the diversity condition -/

/-- The history relation fixes the instantiation of `Q` at every interval up to its time, so that
worlds identical up to `t` agree on `Q` there. -/
def FixesPast (history : HistoricalAlternatives W T) (Q : SortedProperty W E T) : Prop :=
  ∀ t w w', w' ∈ history (w, t) →
    ∀ r : Interval (WithTop T), (∀ x ∈ r, x ≤ ↑t) → (At r w Q ↔ At r w' Q)

theorem fixesPast_eventive :
    FixesPast (Temporal.TWFrame.ofDatedFacts (fun e : E ↦ (τ e).fst) P).alternatives
      (.eventive P) := by
  intro t w w' h r hr
  have key : ∀ e : E, ↑(τ e).withTop ≤ r → (τ e).fst ≤ t := fun e he ↦
    WithTop.coe_le_coe.1 (hr _ (Interval.coe_le_iff.1 he).1)
  exact ⟨fun ⟨e, he, hle⟩ ↦ ⟨e, (h e (key e hle)).1 he, hle⟩,
    fun ⟨e, he, hle⟩ ↦ ⟨e, (h e (key e hle)).2 he, hle⟩⟩

theorem fixesPast_stative :
    FixesPast (Temporal.TWFrame.ofDatedFacts (fun e : E ↦ (τ e).fst) P).alternatives
      (.stative P) := by
  intro t w w' h r hr
  have key : ∀ e : E, ¬ Disjoint (↑(τ e).withTop) r → (τ e).fst ≤ t := fun e hd ↦ by
    obtain ⟨x, hx, hx'⟩ := Interval.not_disjoint_iff.1 hd
    rw [NonemptyInterval.mem_coe_interval, NonemptyInterval.mem_withTop] at hx
    exact WithTop.coe_le_coe.1 (le_trans hx.1 (hr x hx'))
  exact ⟨fun ⟨e, he, hd⟩ ↦ ⟨e, (h e (key e hd)).1 he, hd⟩,
    fun ⟨e, he, hd⟩ ↦ ⟨e, (h e (key e hd)).2 he, hd⟩⟩

theorem settled_perf {history : HistoricalAlternatives W T} (h : FixesPast history Q)
    (cg : Set W) (t : T) : settled history cg t (fun w ↦ At (Interval.Ici ↑t) w (PERF Q)) := by
  intro w _ w' hw'
  refine exists_congr fun r ↦ and_congr_right fun hr ↦ h t w w' hw' r fun x hx ↦ ?_
  exact (hr hx (Interval.mem_Ici.2 le_rfl)).le

theorem settled_present {history : HistoricalAlternatives W T} (h : FixesPast history Q)
    (cg : Set W) (t : T) :
    settled history cg t (fun w ↦ At (Interval.Ici ↑t) w (frame (Interval.pure ↑t) Q)) :=
  fun w _ w' hw' ↦ h t w w' hw' _ fun _ hx ↦ (Interval.mem_pure.1 (Interval.mem_inf.1 hx).2).le

omit [LinearOrder T] in
theorem not_diverse_of_settled {history : HistoricalAlternatives W T} {cg : Set W} {t : T}
    {R : W → Prop} (h : settled history cg t R) : ¬ diverse (metaphysicalBase history) cg t R :=
  settled_not_diverse (fun _ _ _ hw ↦ hw) h

/-! ### The counterfactual implication -/

/-- The paper's footnote assumption says that a past alternative of a common-ground world that is no
alternative at the time of utterance lies outside the common ground. -/
def PastAlternativesOutside (history : HistoricalAlternatives W T) (cg : Set W) (t₀ : T) :
    Prop :=
  ∀ w ∈ cg, ∀ t' ≤ t₀, ∀ w' ∈ metaphysicalBase history w t',
    w' ∉ metaphysicalBase history w t₀ → w' ∉ cg

theorem counterfactual_outside_cg {history : HistoricalAlternatives W T} {cg : Set W} {t₀ : T}
    (h : PastAlternativesOutside history cg t₀) (hw : w ∈ cg)
    (hcf : PRES t₀ (PERF (MAY (metaphysicalBase history) Q)) w)
    (hnow : ∀ t' < t₀, ∀ w' ∈ metaphysicalBase history w t₀, ¬ At (Interval.Ici ↑t') w' Q) :
    ∃ t' < t₀, ∃ w' ∉ cg, w' ∈ metaphysicalBase history w t' ∧ At (Interval.Ici ↑t') w' Q := by
  obtain ⟨t', hlt, w', hw', hat⟩ := pres_perf_may_iff.1 hcf
  exact ⟨t', hlt, w', h w hw t' hlt.le w' hw' (fun hmem ↦ hnow t' hlt w' hmem hat), hw', hat⟩

/-! ### Perspective and orientation -/

/-- A `Scope` is a scoping of a possibility modal with respect to the perfect. -/
inductive Scope
  /-- The modal alone, as in *he may win*. -/
  | modal
  /-- The modal over the perfect, as in *he may have won*, the epistemic reading. -/
  | modalPerf
  /-- The perfect over the modal, as in *he might have won*, the counterfactual reading. -/
  | perfModal
  deriving DecidableEq, Fintype

/-- `s.lf` is the scoping `s` as an operator on the property under the modal. -/
def Scope.lf (MB : W → T → Set W) : Scope → SortedProperty W E T → SortedProperty W E T
  | .modal, Q => MAY MB Q
  | .modalPerf, Q => MAY MB (PERF Q)
  | .perfModal, Q => PERF (MAY MB Q)

/-- `s.perspective` is the time at which the modal base is evaluated, read off the three readings,
the present in `pres_may_eventive_iff` and `pres_may_perf_eventive_iff`, the past time the perfect
supplies in `pres_perf_may_eventive_iff`. -/
def Scope.perspective : Scope → TemporalPerspective
  | .modal | .modalPerf => .present
  | .perfModal => .past

/-- `s.orientation` is the direction of the instantiation from the perspective, read off the three
readings, where the event starts no earlier than the perspective, or ends before it. -/
def Scope.orientation : Scope → TemporalOrientation
  | .modal | .perfModal => .future
  | .modalPerf => .past

theorem Scope.orientation_of_perspective_past :
    ∀ s : Scope, s.perspective = .past → s.orientation = .future := by
  decide

/-! ### A model -/

/-- `winOn d` is the predicate of a winning on day `d`, in a one-world model over integer days. -/
def winOn (d : ℤ) : Unit → NonemptyInterval ℤ → Prop := fun _ e ↦ e = .pure d

/-- The unrestricted modal base admits every world. -/
def anyWorld : Unit → ℤ → Set Unit := fun _ _ ↦ Set.univ

/-- A `Zone` says where a period sits relative to the present. -/
inductive Zone
  | past | present | future
  deriving DecidableEq

/-- `z.day` is the day the zone `z` names, the utterance being on day 0. -/
def Zone.day : Zone → ℤ
  | .past => -1
  | .present => 0
  | .future => 1

/-- The period a zone names is its day. -/
def Zone.period (z : Zone) : Interval (WithTop ℤ) := Interval.pure ↑z.day

/-- `s.zones` are the zones the reference interval of the scoping `s` reaches, the forward interval
of the present, the intervals before it, or the forward interval of a past time. -/
def Scope.zones : Scope → Finset Zone
  | .modal => {.present, .future}
  | .modalPerf => {.past}
  | .perfModal => {.past, .present, .future}

/-- In the model, the scoping's sentence about a winning on the zone's day, framed by that day
and uttered on day 0, is true. -/
def Scope.Sat (s : Scope) (z : Zone) : Prop :=
  PRES 0 (s.lf anyWorld (frame z.period (.eventive (winOn z.day)))) ()

private theorem winOn_at (d : ℤ) {r : Interval (WithTop ℤ)} (h : Interval.pure ↑d ≤ r) :
    At r () (.eventive (winOn d)) :=
  ⟨_, rfl, h⟩

theorem zones_iff : ∀ s : Scope, ∀ z : Zone, z ∈ s.zones ↔ s.Sat z := by
  intro s z
  cases s <;> cases z <;> simp only [Scope.Sat, Scope.lf]
  · refine iff_of_false (by decide) (frame_modal_past ?_ fun x hx y hy ↦ ?_)
    · trivial
    · exact lt_of_le_of_lt (Interval.mem_pure.1 hx).le
        (lt_of_lt_of_le (WithTop.coe_lt_coe.2 (by decide)) (Interval.mem_Ici.1 hy))
  · exact iff_of_true (by decide) (pres_may_iff.2 ⟨(), trivial,
      winOn_at 0 (le_inf (Interval.pure_le_Ici.2 le_rfl) le_rfl)⟩)
  · exact iff_of_true (by decide) (pres_may_iff.2 ⟨(), trivial,
      winOn_at 1 (le_inf (Interval.pure_le_Ici.2 (by decide)) le_rfl)⟩)
  · exact iff_of_true (by decide) (pres_may_iff.2 ⟨(), trivial,
      (NonemptyInterval.pure (-1)).withTop, Interval.precedes_withTop_Ici.2 (by decide),
      winOn_at (-1) (le_inf le_rfl le_rfl)⟩)
  · refine iff_of_false (by decide) (frame_modalPerf_nonpast ?_ (Interval.pure_le_Ici.2 le_rfl))
    trivial
  · refine iff_of_false (by decide)
      (frame_modalPerf_nonpast ?_ (Interval.pure_le_Ici.2 (by decide)))
    trivial
  · exact iff_of_true (by decide) (pres_perf_may_iff.2 ⟨-1, by decide, (), trivial,
      winOn_at (-1) (le_inf (Interval.pure_le_Ici.2 le_rfl) le_rfl)⟩)
  · exact iff_of_true (by decide) (pres_perf_may_iff.2 ⟨-1, by decide, (), trivial,
      winOn_at 0 (le_inf (Interval.pure_le_Ici.2 (by decide)) le_rfl)⟩)
  · exact iff_of_true (by decide) (pres_perf_may_iff.2 ⟨-1, by decide, (), trivial,
      winOn_at 1 (le_inf (Interval.pure_le_Ici.2 (by decide)) le_rfl)⟩)

/-! ### The rows -/

def scopes : List (String × Scope) :=
  [("modal", .modal), ("modalPerf", .modalPerf), ("perfModal", .perfModal)]

/-- An adverbial row records the scoping, the sort of the predicate, and the zone of the frame
adverbial. -/
structure Adverbial where
  /-- The scoping. -/
  scope : Scope
  /-- The sort of the predicate. -/
  sort : Aspect.Dynamicity
  /-- The zone of the period. -/
  zone : Zone

/-- `Adverbial.ofRow row` is the configuration that the adverbial row `row` records. -/
def Adverbial.ofRow (row : Datum) : Option Adverbial := do
  guard (row.feature? "construction" = some "adverb")
  return ⟨← row.parse? "scope" scopes,
    ← row.parse? "sort" [("eventive", Aspect.Dynamicity.dynamic), ("stative", .stative)],
    ← row.parse? "adverb" [("past", Zone.past), ("present", .present), ("future", .future)]⟩

theorem adverb_rows : ∀ row ∈ Examples.all, ∀ a ∈ Adverbial.ofRow row,
    (row.judgment = .ungrammatical ↔ a.zone ∉ a.scope.zones) ∧
      (row.judgment = .questionable ↔
        a.scope = .modal ∧ a.sort = .dynamic ∧ a.zone = .present) := by
  decide

/-- A `Context` records what the context says about the issue. -/
inductive Context
  | settled | unsettled | absent
  deriving DecidableEq

/-- A reading row records the scoping, the zone the instantiation refers to, and the context. -/
structure Reading where
  /-- The scoping. -/
  scope : Scope
  /-- The zone referred to, the present for a stative with *now*. -/
  reference : Zone
  /-- What the context says about the issue. -/
  context : Context

/-- `Reading.ofRow row` is the configuration that the reading row `row` records, and whether the
paper finds the metaphysical reading available. -/
def Reading.ofRow (row : Datum) : Option (Reading × Bool) := do
  guard (row.feature? "construction" = some "reading")
  return (⟨← row.parse? "scope" scopes,
    ← row.parse? "reference" [("past", Zone.past), ("present", .present), ("future", .future)],
    ← row.parse? "context" [("settled", Context.settled), ("open", .unsettled), ("none", .absent)]⟩,
    ← row.parse? "metaphysical" [("available", true), ("unavailable", false)])

/-- The metaphysical base is assignable when the instantiation is neither in the past of the
perspective, `settled_perf`, nor at the present, `settled_present`, nor settled by the
context. -/
def Reading.Metaphysical (r : Reading) : Prop :=
  r.scope ≠ .modalPerf ∧ r.reference ≠ .present ∧ r.context ≠ .settled

instance (r : Reading) : Decidable r.Metaphysical := inferInstanceAs (Decidable (_ ∧ _))

theorem reading_rows : ∀ row ∈ Examples.all, ∀ p ∈ Reading.ofRow row,
    (p.2 = true ↔ p.1.Metaphysical) := by
  decide

/-- A `Complement` is the complement that a phase adverb applies to. -/
inductive Complement
  | eventive | perfect
  deriving DecidableEq

/-- `c.property` is a representative property of the sort of the complement `c`. -/
def Complement.property : Complement → SortedProperty Unit (NonemptyInterval Unit) Unit
  | .eventive => .eventive fun _ _ ↦ True
  | .perfect => PERF (.eventive fun _ _ ↦ True)

/-- A sortal row records the complement of *already* or *yet*. -/
def Complement.ofRow (row : Datum) : Option Complement := do
  guard (row.feature? "construction" = some "sortal")
  return ← row.parse? "complement" [("eventive", Complement.eventive), ("perfect", .perfect)]

theorem sortal_rows : ∀ row ∈ Examples.all, ∀ c ∈ Complement.ofRow row,
    (row.judgment = .acceptable ↔ (phase c.property).isSome = true) := by
  decide

/-- A `Phase` is one of the phase adverbs. -/
inductive Phase
  | already | still
  deriving DecidableEq

/-- A phase row records the adverb scoping over the possibility modal. -/
def Phase.ofRow (row : Datum) : Option Phase := do
  guard (row.feature? "construction" = some "phase")
  return ← row.parse? "adverb" [("already", Phase.already), ("still", .still)]

theorem phase_rows : ∀ row ∈ Examples.all, ∀ p ∈ Phase.ofRow row,
    (row.judgment = .acceptable ↔ p = .still) := by
  decide

/-- An `Order` is one of the German orders of the modal and the perfect auxiliary, which mirror
scope. -/
inductive Order
  /-- *Könnte ... haben* puts the modal over the perfect. -/
  | modalHave
  /-- *Hätte ... können* puts the perfect over the modal. -/
  | hadModal
  deriving DecidableEq

/-- `p.order` is the order that the presuppositions of the adverb `p` require, *schon* the modal
over *already* over the perfect, since *already* can scope neither over a possibility modal,
`not_already_may`, nor under it on an eventive radical, `phase`; *noch* the perfect over *still*
over the modal, on the paper's exclusion of *still* over the perfect. -/
def Phase.order : Phase → Order
  | .already => .modalHave
  | .still => .hadModal

/-- A German row records the order and the adverb. -/
def Order.ofRow (row : Datum) : Option (Order × Phase) := do
  guard (row.feature? "construction" = some "german")
  return (← row.parse? "order" [("modalHave", Order.modalHave), ("hadModal", .hadModal)],
    ← row.parse? "adverb" [("schon", Phase.already), ("noch", .still)])

theorem german_rows : ∀ row ∈ Examples.all, ∀ p ∈ Order.ofRow row,
    (row.judgment = .acceptable ↔ p.1 = p.2.order) := by
  decide

end Condoravdi2002
