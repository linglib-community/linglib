module

public import Linglib.Data.Examples.Toosarvandani2016
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Syntax.Clause.Chaining

/-!
# Toosarvandani (2016): The Temporal Interpretation of Clause Chaining in Northern Paiute

Northern Paiute chains clauses by asyndetic coordination: a marked clause carries the simultaneous
suffix *-na* or the sequential suffix *-si*, relative tenses placing its reference time around its
evaluation time (38) or before it (46), and the coordinator binds that evaluation time to the
reference time of the unmarked clause (§4). The progressive places a reference time within a
nonfinal subpart of the event time (35) and the perfective around it (36), and *-na* selects the
imperfective, which in a marked clause is the progressive (40). A sequential chain of perfectives
thus holds just in case the marked event precedes the unmarked one (59), and a simultaneous chain
of progressives just in case the two overlap (57); linear order plays no part (§4.2), and two
sequential marked clauses are not ordered at all (§4.3).

## Main statements

* `holds_perm`: the truth of a chain does not depend on the order of its marked clauses.
* `exists_holds_iff`, `mem_eventRel_iff`: a chain with one marked clause holds for some reference
  times exactly when its events satisfy the truth condition of its suffix and aspects.
* `sequential_iff`, `simultaneous_iff`: a sequential chain of perfectives holds just in case its
  marked event precedes its unmarked one, and a simultaneous chain of progressives just in case
  they overlap.
* `sequential_unordered`: any two times precede a common later one.
* `rows_agree`: the verdicts of (39), (47), (66) and (71) in their contexts.

## Implementation notes

The suffixes are a `MedialForm` whose timing is their relative tense, each marked clause evaluated
against the unmarked clause rather than the next one. The aspects are `Aspect.Perfectivity`, the
opposition the simultaneous suffix selects on, and the imperfective has the progressive's meaning,
overt (35) or null (41), which the unmarked clause of (39), glossed IPFV, is taken to share. The
contexts are configurations of run times on the natural numbers; the truth conditions compare
endpoints, so they hold there as on any dense copy. Narrative progression (§5) is not formalized.

## References

* [toosarvandani-2016]
-/

@[expose] public section

namespace Toosarvandani2016

open Event (τ)
open Aspect (Perfectivity)
open scoped SetRel

/-! ### Aspect and relative tense -/

/-- The cell of an aspect, the reference time first: within a nonfinal subpart of the event time
for the imperfective, whose meaning is the progressive's (35), (41), and around it for the
perfective (36). -/
def cell : Perfectivity → Finset Allen.Relation
  | .imperfective => Allen.le \ Allen.finalSubinterval
  | .perfective => Aspect.ViewpointType.perfective.cell

/-- The suffixes of a marked clause, the simultaneous *-na* and the sequential *-si*. -/
inductive Suffix where
  | sim
  | seq
  deriving DecidableEq, Repr, Fintype

/-- The relative tense of a suffix, the reference time of the marked clause first: around its
evaluation time (38) or before it (46). -/
def Suffix.timing : Suffix → Finset Allen.Relation
  | .sim => Allen.inv Allen.le
  | .seq => Allen.precedes

/-- The suffixes are medial forms that mark no switch-reference, which Northern Paiute lacks. -/
instance : MedialForm Suffix where
  sr _ := none
  relations
    | .sim => {.simultaneous}
    | .seq => {.sequential}
  timing := Suffix.timing
  IndexesSubject _ := False

/-- The simultaneous suffix selects the imperfective, the sequential suffix either aspect (40). -/
def Suffix.Selects : Suffix → Perfectivity → Prop
  | .sim, p => p = .imperfective
  | .seq, _ => True

instance : ∀ s p, Decidable (Suffix.Selects s p)
  | .sim, _ => inferInstanceAs (Decidable (_ = _))
  | .seq, _ => instDecidableTrue

section

variable {T : Type*} [LinearOrder T] {t₁ t s : NonemptyInterval T}

@[simp] theorem mem_cell_imperfective :
    (t, s) ∈ Allen.toSetRel (cell .imperfective) ↔ s.fst ≤ t.fst ∧ t.snd < s.snd := by
  simp only [cell, Allen.mem_toSetRel, Finset.mem_sdiff, Allen.relation_mem_le,
    Allen.relation_mem_finalSubinterval, NonemptyInterval.FinalSubinterval,
    NonemptyInterval.le_def]
  exact ⟨fun ⟨⟨h₁, h₂⟩, h₃⟩ ↦ ⟨h₁, h₂.lt_of_ne fun h ↦ h₃ ⟨⟨h₁, h₂⟩, h⟩⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨⟨h₁, h₂.le⟩, fun h ↦ h₂.ne h.2⟩⟩

@[simp] theorem mem_cell_perfective :
    (t, s) ∈ Allen.toSetRel (cell .perfective) ↔ t.fst ≤ s.fst ∧ s.snd ≤ t.snd := by
  rw [show cell .perfective = Aspect.ViewpointType.perfective.cell from rfl,
    ← Aspect.ViewpointType.ttTSitRelation_iff]
  exact NonemptyInterval.le_def

@[simp] theorem mem_timing_sim :
    (t₁, t) ∈ Allen.toSetRel (MedialForm.timing Suffix.sim) ↔ t₁.fst ≤ t.fst ∧ t.snd ≤ t₁.snd := by
  change (t₁, t) ∈ Allen.toSetRel (Allen.inv Allen.le) ↔ _
  simp [NonemptyInterval.le_def]

@[simp] theorem mem_timing_seq :
    (t₁, t) ∈ Allen.toSetRel (MedialForm.timing Suffix.seq) ↔ t₁.snd < t.fst := by
  change (t₁, t) ∈ Allen.toSetRel Allen.precedes ↔ _
  simp [NonemptyInterval.Precedes]

end

/-! ### Clause chains -/

section

variable {T : Type*} [LinearOrder T] {W E : Type*} [Event.TemporalTrace E T]

/-- The operator of an aspect: the reference times at which it places an event of the
predicate. -/
def denote (p : Perfectivity) (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  Aspect.ofRel (fun t s ↦ (t, s) ∈ Allen.toSetRel (cell p)) P

/-- A marked clause: its suffix, its aspect and its predicate of events. -/
structure Marked (W E : Type*) where
  /-- The suffix. -/
  suffix : Suffix
  /-- The aspect. -/
  aspect : Perfectivity
  /-- The predicate of events. -/
  pred : W → E → Prop

/-- A chain holds at world `w` and time `t` when its unmarked clause, of aspect `b` and predicate
`Q`, holds at `t`, and each marked clause holds at the reference time the context gives it, which
stands to `t` as the clause's suffix says (56). -/
def Holds (cs : List (Marked W E × NonemptyInterval T)) (b : Perfectivity) (Q : W → E → Prop)
    (w : W) (t : NonemptyInterval T) : Prop :=
  (∀ c ∈ cs, c.2 ∈ denote c.1.aspect c.1.pred w ∧
    (c.2, t) ∈ Allen.toSetRel (MedialForm.timing c.1.suffix)) ∧ t ∈ denote b Q w

theorem holds_perm {cs cs' : List (Marked W E × NonemptyInterval T)} (h : cs.Perm cs')
    {b : Perfectivity} {Q : W → E → Prop} {w : W} {t : NonemptyInterval T} :
    Holds cs b Q w t ↔ Holds cs' b Q w t := by
  simp only [Holds, h.mem_iff]

end

section

variable {T : Type*} [LinearOrder T]

/-- How the event of a marked clause with suffix `s` and aspect `a` may stand to the event of an
unmarked clause of aspect `b`: through the reference times of the two clauses. -/
def eventRel (s : Suffix) (a b : Perfectivity) :
    SetRel (NonemptyInterval T) (NonemptyInterval T) :=
  (Allen.toSetRel (cell a)).inv ○ Allen.toSetRel (MedialForm.timing s) ○ Allen.toSetRel (cell b)

/-- The truth condition of a chain with one marked clause on the run times `i` of its marked event
and `j` of its unmarked event. -/
def TruthCondition (i j : NonemptyInterval T) : Suffix → Perfectivity → Perfectivity → Prop
  | .sim, .imperfective, .imperfective =>
    i.fst < j.snd ∧ j.fst < i.snd ∧ i.fst < i.snd ∧ j.fst < j.snd
  | .sim, .imperfective, .perfective => i.fst ≤ j.fst ∧ j.snd < i.snd
  | .sim, .perfective, .imperfective => j.fst < j.snd
  | .sim, .perfective, .perfective => True
  | .seq, .imperfective, .imperfective => i.fst < j.snd ∧ i.fst < i.snd ∧ j.fst < j.snd
  | .seq, .imperfective, .perfective => i.fst < j.fst ∧ i.fst < i.snd
  | .seq, .perfective, .imperfective => i.snd < j.snd ∧ j.fst < j.snd
  | .seq, .perfective, .perfective => i.Precedes j

instance (i j : NonemptyInterval T) :
    ∀ s a b, Decidable (TruthCondition i j s a b)
  | .sim, .imperfective, .imperfective | .sim, .imperfective, .perfective
  | .sim, .perfective, .imperfective | .seq, .imperfective, .imperfective
  | .seq, .imperfective, .perfective | .seq, .perfective, .imperfective
  | .seq, .perfective, .perfective => by unfold TruthCondition; infer_instance
  | .sim, .perfective, .perfective => instDecidableTrue

theorem mem_eventRel_iff [DenselyOrdered T] {i j : NonemptyInterval T} {s : Suffix}
    {a b : Perfectivity} : (i, j) ∈ eventRel s a b ↔ TruthCondition i j s a b := by
  have hi := i.fst_le_snd
  have hj := j.fst_le_snd
  cases s <;> cases a <;> cases b <;>
    simp only [eventRel, SetRel.mem_comp, SetRel.mem_inv, mem_cell_imperfective,
      mem_cell_perfective, mem_timing_sim, mem_timing_seq, TruthCondition,
      NonemptyInterval.Precedes]
  · exact ⟨fun _ ↦ trivial, fun _ ↦ ⟨j, ⟨i ⊔ j, NonemptyInterval.le_def.1 le_sup_left,
      NonemptyInterval.le_def.1 le_sup_right⟩, le_rfl, le_rfl⟩⟩
  · constructor
    · rintro ⟨t, -, h₅, h₆⟩
      exact h₅.trans_lt (t.fst_le_snd.trans_lt h₆)
    · intro h
      exact ⟨.pure j.fst, ⟨i ⊔ .pure j.fst, NonemptyInterval.le_def.1 le_sup_left,
        NonemptyInterval.le_def.1 le_sup_right⟩, le_rfl, h⟩
  · constructor
    · rintro ⟨t, ⟨t₁, ⟨h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩
      exact ⟨(h₁.trans h₃).trans h₅, (h₆.trans h₄).trans_lt h₂⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨j, ⟨j, ⟨h₁, h₂⟩, le_rfl, le_rfl⟩, le_rfl, le_rfl⟩
  · constructor
    · rintro ⟨t, ⟨t₁, ⟨h₁, h₂⟩, h₃, h₄⟩, h₅, h₆⟩
      have ht := t.fst_le_snd
      exact ⟨(h₁.trans h₃).trans_lt (ht.trans_lt h₆), h₅.trans_lt (ht.trans_lt (h₄.trans_lt h₂)),
        h₁.trans_lt (t₁.fst_le_snd.trans_lt h₂), h₅.trans_lt (ht.trans_lt h₆)⟩
    · rintro ⟨h₁, h₂, h₃, h₄⟩
      exact ⟨.pure (max i.fst j.fst), ⟨.pure (max i.fst j.fst),
        ⟨le_max_left _ _, max_lt h₃ h₂⟩, le_rfl, le_rfl⟩, le_max_right _ _, max_lt h₁ h₄⟩
  · constructor
    · rintro ⟨t, ⟨t₁, ⟨h₁, h₂⟩, h₃⟩, h₅, h₆⟩
      exact h₂.trans_lt (h₃.trans_le h₅)
    · intro h
      exact ⟨j, ⟨i, ⟨le_rfl, le_rfl⟩, h⟩, le_rfl, le_rfl⟩

  · constructor
    · rintro ⟨t, ⟨t₁, ⟨h₁, h₂⟩, h₃⟩, h₅, h₆⟩
      exact ⟨h₂.trans_lt (h₃.trans_le (t.fst_le_snd.trans h₆.le)),
        h₅.trans_lt (t.fst_le_snd.trans_lt h₆)⟩
    · rintro ⟨h₁, h₂⟩
      obtain ⟨b, hb, hjb, hbj⟩ : ∃ b, i.snd < b ∧ j.fst ≤ b ∧ b < j.snd := by
        rcases lt_or_ge i.snd j.fst with h | h
        · exact ⟨j.fst, h, le_rfl, h₂⟩
        · obtain ⟨b, hb₁, hb₂⟩ := exists_between h₁
          exact ⟨b, hb₁, h.trans hb₁.le, hb₂⟩
      exact ⟨.pure b, ⟨i, ⟨le_rfl, le_rfl⟩, hb⟩, hjb, hbj⟩
  · constructor
    · rintro ⟨t, ⟨t₁, ⟨h₁, h₂⟩, h₃⟩, h₅, h₆⟩
      exact ⟨(h₁.trans t₁.fst_le_snd).trans_lt (h₃.trans_le h₅),
        h₁.trans_lt (t₁.fst_le_snd.trans_lt h₂)⟩
    · rintro ⟨h₁, h₂⟩
      exact ⟨j, ⟨.pure i.fst, ⟨le_rfl, h₂⟩, h₁⟩, le_rfl, le_rfl⟩
  · constructor
    · rintro ⟨t, ⟨t₁, ⟨h₁, h₂⟩, h₃⟩, h₅, h₆⟩
      have ht := t.fst_le_snd
      exact ⟨(h₁.trans t₁.fst_le_snd).trans_lt (h₃.trans_le (ht.trans h₆.le)),
        h₁.trans_lt (t₁.fst_le_snd.trans_lt h₂), h₅.trans_lt (ht.trans_lt h₆)⟩
    · rintro ⟨h₁, h₂, h₃⟩
      obtain ⟨b, hb, hjb, hbj⟩ : ∃ b, i.fst < b ∧ j.fst ≤ b ∧ b < j.snd := by
        rcases lt_or_ge i.fst j.fst with h | h
        · exact ⟨j.fst, h, le_rfl, h₃⟩
        · obtain ⟨b, hb₁, hb₂⟩ := exists_between h₁
          exact ⟨b, hb₁, h.trans hb₁.le, hb₂⟩
      exact ⟨.pure b, ⟨.pure i.fst, ⟨le_rfl, h₂⟩, hb⟩, hjb, hbj⟩
end

section

variable {T : Type*} [LinearOrder T] {W E : Type*} [Event.TemporalTrace E T] {s : Suffix}
  {a b : Perfectivity} {P Q : W → E → Prop} {w : W}

theorem exists_holds_iff :
    (∃ t₁ t : NonemptyInterval T, Holds [(⟨s, a, P⟩, t₁)] b Q w t) ↔
      ∃ e e' : E, P w e ∧ Q w e' ∧ (τ e, τ e') ∈ eventRel s a b := by
  simp only [Holds, eventRel, denote, List.mem_singleton, forall_eq, Aspect.mem_ofRel,
    SetRel.mem_comp, SetRel.mem_inv]
  constructor
  · rintro ⟨t₁, t, ⟨⟨e, h₁, hP⟩, h₂⟩, e', h₃, hQ⟩
    exact ⟨e, e', hP, hQ, t, ⟨t₁, h₁, h₂⟩, h₃⟩
  · rintro ⟨e, e', hP, hQ, t, ⟨t₁, h₁, h₂⟩, h₃⟩
    exact ⟨t₁, t, ⟨⟨e, h₁, hP⟩, h₂⟩, e', h₃, hQ⟩

variable [DenselyOrdered T]

/-- A sequential chain of perfectives holds just in case the marked event precedes the unmarked
one (59). -/
theorem sequential_iff :
    (∃ t₁ t : NonemptyInterval T, Holds [(⟨.seq, .perfective, P⟩, t₁)] .perfective Q w t) ↔
      ∃ e e' : E, P w e ∧ Q w e' ∧ (τ e).Precedes (τ e') := by
  simp only [exists_holds_iff, mem_eventRel_iff, TruthCondition]

/-- A simultaneous chain of progressives holds just in case the two events, neither a point,
overlap in more than a point (57). -/
theorem simultaneous_iff :
    (∃ t₁ t : NonemptyInterval T, Holds [(⟨.sim, .imperfective, P⟩, t₁)] .imperfective Q w t) ↔
      ∃ e e' : E, P w e ∧ Q w e' ∧ (τ e).fst < (τ e').snd ∧ (τ e').fst < (τ e).snd ∧
        (τ e).fst < (τ e).snd ∧ (τ e').fst < (τ e').snd := by
  simp only [exists_holds_iff, mem_eventRel_iff, TruthCondition]

end

theorem sequential_unordered {T : Type*} [LinearOrder T] [NoMaxOrder T]
    (t₁ t₂ : NonemptyInterval T) :
    ∃ t, (t₁, t) ∈ Allen.toSetRel (MedialForm.timing Suffix.seq) ∧
      (t₂, t) ∈ Allen.toSetRel (MedialForm.timing Suffix.seq) := by
  obtain ⟨b, hb⟩ := exists_gt (max t₁.snd t₂.snd)
  exact ⟨.pure b, mem_timing_seq.2 ((le_max_left _ _).trans_lt hb),
    mem_timing_seq.2 ((le_max_right _ _).trans_lt hb)⟩

/-! ### The verdicts -/

/-- The events of the contexts of (39), of (47) and (66), and of (71). -/
inductive Ev where
  | bathe
  | watch
  | escape
  | wakeUp
  | miss
  | play
  | dance
  | enter
  deriving DecidableEq, Repr

/-- Run times the contexts fix: the dog watches the boy in the bathtub; the frog escapes while the
boy sleeps, and he notices after waking; the boy and the girl play and dance at the same time and
stop before their mother comes home. -/
def Ev.time : Ev → NonemptyInterval ℕ
  | .bathe => ⟨(0, 4), by decide⟩
  | .watch => ⟨(1, 3), by decide⟩
  | .escape => ⟨(0, 1), by decide⟩
  | .wakeUp => ⟨(2, 3), by decide⟩
  | .miss => ⟨(4, 5), by decide⟩
  | .play => ⟨(0, 3), by decide⟩
  | .dance => ⟨(0, 3), by decide⟩
  | .enter => ⟨(4, 5), by decide⟩

/-- What a row's verdict depends on: the suffix and aspect of its marked clauses and their events,
and the aspect and event of its unmarked clause. -/
structure Config where
  suffix : Suffix
  aspect : Perfectivity
  marked : List Ev
  unmarkedAspect : Perfectivity
  unmarked : Ev

/-- The aspect columns of the rows. -/
def aspects : List (String × Perfectivity) :=
  [("prog", .imperfective), ("ipfv", .imperfective), ("pfv", .perfective)]

/-- The event columns of the rows. -/
def events : List (String × Ev) :=
  [("bathe", .bathe), ("watch", .watch), ("escape", .escape), ("wakeUp", .wakeUp),
    ("miss", .miss), ("play", .play), ("dance", .dance), ("enter", .enter)]

/-- The configuration of a row, read from its stimulus columns. -/
def config (e : Datum) : Option Config := do
  let s ← e.parse? "suffix" [("sim", .sim), ("seq", .seq)]
  let a ← e.parse? "aspect" aspects
  let b ← e.parse? "unmarkedAspect" aspects
  let u ← e.parse? "unmarkedEvent" events
  let ms ← (e.features "markedEvent").mapM (List.lookup · events)
  pure ⟨s, a, ms, b, u⟩

/-- The predicted verdict: each marked event and the unmarked event meet the truth condition. -/
def Config.verdict (c : Config) : Bool :=
  decide (∀ m ∈ c.marked,
    TruthCondition m.time c.unmarked.time c.suffix c.aspect c.unmarkedAspect)

/-- The verdicts of (39), (47), (66) and (71) are those the truth conditions predict. -/
theorem rows_agree : ∀ e ∈ Examples.all, e.FitsVerdict config Config.verdict := by
  decide

/-- The simultaneous suffix takes the imperfective (40b) and not the perfective (40c). -/
theorem selection :
    (Examples.ex_40b.judgment = .acceptable ↔ Suffix.sim.Selects .imperfective) ∧
      (Examples.ex_40c.judgment = .ungrammatical ↔ ¬ Suffix.sim.Selects .perfective) := by
  decide

end Toosarvandani2016
