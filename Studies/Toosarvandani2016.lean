module

public import Linglib.Data.Examples.Toosarvandani2016
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Syntax.Clause.Chaining

/-!
# Toosarvandani (2016): The Temporal Interpretation of Clause Chaining in Northern Paiute

Northern Paiute chains clauses by asyndetic coordination: a marked clause carries the simultaneous
suffix *-na* or the sequential suffix *-si*, relative tenses placing its reference time around its
evaluation time (38) or before it (46), and the coordinator binds that evaluation time to the
reference time of the unmarked clause (§4). Aspect places a reference time within a nonfinal
subpart of the event time (35) or around it (36), and *-na* selects the former (40). A sequential
chain of perfectives thus holds just in case the marked event precedes the unmarked one (59), and
a simultaneous chain of progressives just in case the two overlap (57); linear order plays no part
(§4.2), and two sequential marked clauses are not ordered at all (§4.3).

## Main statements

* `holds_perm`: the truth of a chain does not depend on the order of its marked clauses.
* `exists_holds_iff`: on dense time, a chain with one marked clause holds for some reference times
  exactly when its two events stand in the composite cell.
* `sequential_iff`, `simultaneous_iff`: a sequential chain of perfectives holds just in case its
  marked event precedes its unmarked one, and a simultaneous chain of progressives just in case
  they overlap.
* `sequential_unordered`: two times before a third may stand in any relation.
* `rows_agree`: the verdicts of (39), (47), (66) and (71) in their contexts.

## Implementation notes

The suffixes are a `MedialForm` whose timing is their relative tense, each marked clause evaluated
against the unmarked clause rather than the next one. The unmarked imperfective of (39), glossed
IPFV, gets the meaning the paper gives *-wɨnnɨ* (35), and the contexts are configurations of run
times that their descriptions fix. Narrative progression (§5) is not formalized.

## References

* [toosarvandani-2016]
-/

@[expose] public section

namespace Toosarvandani2016

open Event (τ)

/-! ### Aspect and relative tense -/

/-- The aspects of a clause, overt as the progressive *-wɨnnɨ* and the perfective *-hu* or carried
by a null head with the same meaning. -/
inductive Viewpoint where
  | progressive
  | perfective
  deriving DecidableEq, Repr, Fintype

/-- The cell of an aspect, the reference time first: within a nonfinal subpart of the event time
for the progressive (35), around it for the perfective (36). -/
def Viewpoint.cell : Viewpoint → Finset Allen.Relation
  | .progressive => Allen.atoms.filter fun r ↦ r.fstFst ≠ .lt ∧ r.sndSnd = .lt
  | .perfective => Aspect.ViewpointType.perfective.cell

theorem relation_mem_progressive {T : Type*} [LinearOrder T] {t s : NonemptyInterval T} :
    Allen.relation t s ∈ Viewpoint.progressive.cell ↔ s.fst ≤ t.fst ∧ t.snd < s.snd := by
  rw [Viewpoint.cell, Allen.relation_mem_filter]
  simp [Allen.relation, Allen.ofEndpoints, compare_lt_iff_lt]

/-- The operator of an aspect: the reference times at which it places an event of the
predicate. -/
def Viewpoint.denote {T : Type*} [LinearOrder T] {W E : Type*} [Event.TemporalTrace E T]
    (v : Viewpoint) (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  Aspect.ofRel (fun t s ↦ (t, s) ∈ Allen.toSetRel v.cell) P

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

/-- The simultaneous suffix selects imperfective aspect, the sequential suffix either (40). -/
def Suffix.Selects : Suffix → Viewpoint → Prop
  | .sim, v => v = .progressive
  | .seq, _ => True

instance : ∀ s v, Decidable (Suffix.Selects s v)
  | .sim, _ => inferInstanceAs (Decidable (_ = _))
  | .seq, _ => instDecidableTrue

/-! ### Clause chains -/

section

variable {T : Type*} [LinearOrder T] {W E : Type*} [Event.TemporalTrace E T]

/-- A marked clause: its suffix, its aspect and its predicate of events. -/
structure Marked (W E : Type*) where
  /-- The suffix. -/
  suffix : Suffix
  /-- The aspect. -/
  aspect : Viewpoint
  /-- The predicate of events. -/
  pred : W → E → Prop

/-- A chain holds at world `w` and time `t` when its unmarked clause, of aspect `v` and predicate
`Q`, holds at `t`, and each marked clause holds at the reference time the context gives it, which
stands to `t` as the clause's suffix says (56). -/
def Holds (cs : List (Marked W E × NonemptyInterval T)) (v : Viewpoint) (Q : W → E → Prop)
    (w : W) (t : NonemptyInterval T) : Prop :=
  (∀ c ∈ cs, c.2 ∈ c.1.aspect.denote c.1.pred w ∧
    (c.2, t) ∈ Allen.toSetRel (MedialForm.timing c.1.suffix)) ∧ t ∈ v.denote Q w

theorem holds_perm {cs cs' : List (Marked W E × NonemptyInterval T)} (h : cs.Perm cs')
    {v : Viewpoint} {Q : W → E → Prop} {w : W} {t : NonemptyInterval T} :
    Holds cs v Q w t ↔ Holds cs' v Q w t := by
  simp only [Holds, h.mem_iff]

end

/-- The cell in which the event of a marked clause with suffix `s` and aspect `a` stands to the
event of an unmarked clause of aspect `b`: through the reference times of the two clauses. -/
def eventCell (s : Suffix) (a b : Viewpoint) : Finset Allen.Relation :=
  Allen.comp (Allen.comp (Allen.inv a.cell) s.timing) b.cell

theorem exists_holds_iff {T : Type*} [LinearOrder T] [DenselyOrdered T] [NoMinOrder T]
    [NoMaxOrder T] {W E : Type*} [Event.TemporalTrace E T] {s : Suffix} {a b : Viewpoint}
    {P Q : W → E → Prop} {w : W} :
    (∃ t₁ t : NonemptyInterval T, Holds [(⟨s, a, P⟩, t₁)] b Q w t) ↔
      ∃ e e' : E, P w e ∧ Q w e' ∧ (τ e, τ e') ∈ Allen.toSetRel (eventCell s a b) := by
  simp only [Holds, eventCell, Allen.toSetRel_comp, Allen.toSetRel_inv, List.mem_singleton,
    forall_eq, Viewpoint.denote, Aspect.mem_ofRel, SetRel.mem_comp, SetRel.mem_inv]
  constructor
  · rintro ⟨t₁, t, ⟨⟨e, h₁, hP⟩, h₂⟩, e', h₃, hQ⟩
    exact ⟨e, e', hP, hQ, t, ⟨t₁, h₁, h₂⟩, h₃⟩
  · rintro ⟨e, e', hP, hQ, t, ⟨t₁, h₁, h₂⟩, h₃⟩
    exact ⟨t₁, t, ⟨⟨e, h₁, hP⟩, h₂⟩, e', h₃, hQ⟩

/-! ### The truth conditions -/

section

variable {T : Type*} [LinearOrder T] {W E : Type*} [Event.TemporalTrace E T] {P Q : W → E → Prop}
  {w : W}

/-- A sequential chain of perfectives holds just in case the marked event precedes the unmarked
one (59). -/
theorem sequential_iff :
    (∃ t₁ t : NonemptyInterval T, Holds [(⟨.seq, .perfective, P⟩, t₁)] .perfective Q w t) ↔
      ∃ e e' : E, P w e ∧ Q w e' ∧ (τ e).Precedes (τ e') := by
  simp only [Holds, List.mem_singleton, forall_eq, Viewpoint.denote, Aspect.mem_ofRel,
    Viewpoint.cell, ← Aspect.ViewpointType.ttTSitRelation_iff,
    Aspect.ViewpointType.ttTSitRelation]
  change (∃ t₁ t, ((∃ e, τ e ≤ t₁ ∧ P w e) ∧ (t₁, t) ∈ Allen.toSetRel Allen.precedes) ∧
    ∃ e, τ e ≤ t ∧ Q w e) ↔ _
  simp only [Allen.mem_toSetRel, Allen.relation_mem_precedes]
  constructor
  · rintro ⟨t₁, t, ⟨⟨e, he, hP⟩, h⟩, e', he', hQ⟩
    exact ⟨e, e', hP, hQ, NonemptyInterval.precedes_of_le_of_precedes he
      ((NonemptyInterval.le_def.1 he').1 |> fun h' ↦ lt_of_lt_of_le h h')⟩
  · rintro ⟨e, e', hP, hQ, h⟩
    exact ⟨τ e, τ e', ⟨⟨e, le_rfl, hP⟩, h⟩, e', le_rfl, hQ⟩

/-- A simultaneous chain of progressives holds just in case the two events, neither a point,
overlap in more than a point (57). -/
theorem simultaneous_iff :
    (∃ t₁ t : NonemptyInterval T, Holds [(⟨.sim, .progressive, P⟩, t₁)] .progressive Q w t) ↔
      ∃ e e' : E, P w e ∧ Q w e' ∧ (τ e).fst < (τ e').snd ∧ (τ e').fst < (τ e).snd ∧
        (τ e).fst < (τ e).snd ∧ (τ e').fst < (τ e').snd := by
  simp only [Holds, List.mem_singleton, forall_eq, Viewpoint.denote, Aspect.mem_ofRel,
    Allen.mem_toSetRel, relation_mem_progressive]
  change (∃ t₁ t, ((∃ e, ((τ e).fst ≤ t₁.fst ∧ t₁.snd < (τ e).snd) ∧ P w e) ∧
    (t₁, t) ∈ Allen.toSetRel (Allen.inv Allen.le)) ∧
    ∃ e, ((τ e).fst ≤ t.fst ∧ t.snd < (τ e).snd) ∧ Q w e) ↔ _
  simp only [Allen.toSetRel_inv, SetRel.mem_inv, Allen.mem_toSetRel, Allen.relation_mem_le,
    NonemptyInterval.le_def]
  constructor
  · rintro ⟨t₁, t, ⟨⟨e, ⟨h₁, h₂⟩, hP⟩, h₃, h₄⟩, e', ⟨h₅, h₆⟩, hQ⟩
    have h := t.fst_le_snd
    exact ⟨e, e', hP, hQ, (h₁.trans h₃).trans_lt (h.trans_lt h₆),
      h₅.trans_lt (h.trans_lt (h₄.trans_lt h₂)), h₁.trans_lt (t₁.fst_le_snd.trans_lt h₂),
      h₅.trans_lt (h.trans_lt h₆)⟩
  · rintro ⟨e, e', hP, hQ, h₁, h₂, h₃, h₄⟩
    let p := max (τ e).fst (τ e').fst
    refine ⟨NonemptyInterval.pure p, NonemptyInterval.pure p,
      ⟨⟨e, ⟨le_max_left _ _, max_lt h₃ h₂⟩, hP⟩, le_rfl, le_rfl⟩, e',
      ⟨le_max_right _ _, max_lt h₁ h₄⟩, hQ⟩

end

theorem sequential_unordered :
    Allen.comp Allen.precedes (Allen.inv Allen.precedes) = Allen.atoms := by
  decide +kernel

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
  aspect : Viewpoint
  marked : List Ev
  unmarkedAspect : Viewpoint
  unmarked : Ev

/-- The aspect columns of the rows, the imperfective read as the progressive. -/
def aspects : List (String × Viewpoint) :=
  [("prog", .progressive), ("ipfv", .progressive), ("pfv", .perfective)]

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

/-- The predicted verdict: each marked event stands to the unmarked event in the composite cell. -/
def Config.verdict (c : Config) : Bool :=
  decide (∀ m ∈ c.marked,
    Allen.relation m.time c.unmarked.time ∈ eventCell c.suffix c.aspect c.unmarkedAspect)

/-- The verdicts of (39), (47), (66) and (71) are those the composite cells predict. -/
theorem rows_agree : ∀ e ∈ Examples.all, e.FitsVerdict config Config.verdict := by
  decide +kernel

/-- The simultaneous suffix takes the progressive (40b) and not the perfective (40c). -/
theorem selection :
    (Examples.ex_40b.judgment = .acceptable ↔ Suffix.sim.Selects .progressive) ∧
      (Examples.ex_40c.judgment = .ungrammatical ↔ ¬ Suffix.sim.Selects .perfective) := by
  decide

end Toosarvandani2016
