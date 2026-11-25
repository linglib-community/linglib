module

public import Linglib.Semantics.Aspect.Viewpoint.Defs
public import Linglib.Semantics.Aspect.Perfect
public import Linglib.Semantics.Events.RunTimes

/-!
# Viewpoint aspect

A viewpoint relates the topic time to the situation time. This file defines the operators of
viewpoint aspect, which take a predicate of events to an interval property, as possibility
`◇[R]` along a relation `R` between intervals.

The run times of an event predicate `P` form the interval property `Event.runTimes P`. A viewpoint
`v` has a cell `v.cell` of the interval algebra, and its operator `v.denote P` is possibility along
that cell applied to `runTimes P`. The perfective `perfective P` holds at `t` when some run time
lies within `t`, so that `perfective P = inclusive (runTimes P)`, and the non-strict imperfective
`unbounded P` when `t` lies within some run time. The modal imperfective `imperfective acc P w`
holds at `t` when `unbounded (P v) t` holds in every world `v` accessible from `w` along `acc t`.

Possibility along a relation is left adjoint to necessity along its converse, which gives
`unbounded_le_iff`: `unbounded P ≤ q ↔ runTimes P ≤ durative q`. The perfective is closed under
superintervals and the non-strict imperfective under subintervals.

## Implementation notes

* A cell says how the interval an operator introduces stands to the reference interval, as the
  relation of a tense says how the time it introduces stands to the evaluation time, so the
  operator along a cell `C` is `◇[toSetRel C]`. Klein states the relations in the converse
  order, the topic time first.
* Only the modal imperfective reads the world; a predicate with a world argument is applied to
  it, `perfective (P w)`.
* Smith's neutral viewpoint includes the initial point of the situation and at least one internal
  stage where the situation has stages: the topic time contains the start of the situation and,
  when the situation is not instantaneous, reaches past it.
* The accessibility relation of the imperfective depends on the reference interval: Ferreira's
  best worlds of a circumstantial base, Deo's inertia histories, or the language-specific modal
  bases of Arregui, Rivero and Salanova.

## References

* [smith-1997]
* [klein-1994]
* [ferreira-2016]
* [deo-2009]
* [arregui-rivero-salanova-2014]
* [knick-sharf-2026]
* [pancheva-2003]
-/

@[expose] public section

namespace Aspect

open ModalLogic IntervalAlgebra Allen Temporal
open scoped SetRel

/-! ### The cell of a viewpoint -/

/-- The cell of a viewpoint says how the situation time stands to the topic time: around it,
within it, before it or up to its start, after it or from its end, and, for the neutral
viewpoint, starting within it and, when the situation takes time, before its end. -/
def ViewpointType.cell : ViewpointType → IntervalAlgebra
  | .imperfective => IntervalAlgebra.lt⁻¹
  | .perfective => IntervalAlgebra.le
  | .perfect => IntervalAlgebra.isBefore
  | .prospective => IntervalAlgebra.isBefore⁻¹
  | .neutral =>
    IntervalAlgebra.startsWithin ⊓ .ofPred fun r ↦ r.firstShape = .lt → r.fstSnd = .lt

section Cell

variable {T : Type*} [LinearOrder T] {tt tsit : NonemptyInterval T}

@[simp] theorem ViewpointType.relation_mem_cell_imperfective :
    relation tsit tt ∈ ViewpointType.imperfective.cell ↔ tt < tsit := by
  simp [cell]

@[simp] theorem ViewpointType.relation_mem_cell_perfective :
    relation tsit tt ∈ ViewpointType.perfective.cell ↔ tsit ≤ tt := by
  simp [cell]

@[simp] theorem ViewpointType.relation_mem_cell_perfect :
    relation tsit tt ∈ ViewpointType.perfect.cell ↔ tsit.snd ≤ tt.fst := by
  simp [cell]

@[simp] theorem ViewpointType.relation_mem_cell_prospective :
    relation tsit tt ∈ ViewpointType.prospective.cell ↔ tt.snd ≤ tsit.fst := by
  simp [cell]

@[simp] theorem ViewpointType.relation_mem_cell_neutral :
    relation tsit tt ∈ ViewpointType.neutral.cell ↔
      tsit.fst ∈ tt ∧ (tsit.fst < tsit.snd → tsit.fst < tt.snd) := by
  simp [cell, Allen.ofEndpoints, compare_lt_iff_lt]

end Cell

open Event (τ runTimes runTimes_iff runTimes_τ runTimes_mono diamond_runTimes_iff)

variable {T : Type*} [LinearOrder T] {W E : Type*} [TemporalTrace E T]
  {P P' : E → Prop} {p q : NonemptyInterval T → Prop} {s t : NonemptyInterval T}

/-! ### The operators of the viewpoints -/

/-- The operator of a viewpoint holds at a topic time to which the run time of some event of the
predicate stands in the viewpoint's cell. -/
def ViewpointType.denote (v : ViewpointType) (P : E → Prop) : NonemptyInterval T → Prop :=
  ◇[toSetRel v.cell] (runTimes P)

theorem ViewpointType.denote_iff {v : ViewpointType} :
    v.denote P t ↔ ∃ e, relation (τ e) t ∈ v.cell ∧ P e := by
  simp [denote, diamond_runTimes_iff]

theorem ViewpointType.denote_mono (v : ViewpointType) :
    Monotone (v.denote : (E → Prop) → NonemptyInterval T → Prop) :=
  (diamond_mono _).comp runTimes_mono

/-- The perfective holds where the run time of an event of the predicate lies within the
reference time. -/
def perfective (P : E → Prop) : NonemptyInterval T → Prop := inclusive (runTimes P)

/-- The non-strict imperfective, (7b) of [pancheva-2003], holds where the reference time lies
within the run time of an event of the predicate. -/
def unbounded (P : E → Prop) : NonemptyInterval T → Prop := ◇[(toSetRel .le).inv] (runTimes P)

/-- The imperfective holds at a reference interval `t` in `w` when, in every world accessible
from `w` along `acc t`, `t` lies within the run time of an event of the predicate. The event need
not be actual, so an event in progress need never be completed. -/
def imperfective (acc : NonemptyInterval T → SetRel W W) (P : W → E → Prop) (w : W) :
    NonemptyInterval T → Prop :=
  fun t ↦ □[acc t] (fun v ↦ unbounded (P v) t) w

theorem perfective_iff : perfective P t ↔ ∃ e, τ e ≤ t ∧ P e := by
  simp [perfective, inclusive, diamond_runTimes_iff]

theorem unbounded_iff : unbounded P t ↔ ∃ e, t ≤ τ e ∧ P e := by
  simp [unbounded, diamond_runTimes_iff]

theorem denote_prospective_iff :
    ViewpointType.prospective.denote P t ↔ ∃ e, t.snd ≤ (τ e).fst ∧ P e := by
  simp [ViewpointType.denote_iff]

theorem imperfective_iff {acc : NonemptyInterval T → SetRel W W} {P : W → E → Prop} {w : W} :
    imperfective acc P w t ↔ ∀ v, w ~[acc t] v → ∃ e, t ≤ τ e ∧ P v e :=
  forall₂_congr fun _ _ ↦ unbounded_iff

theorem denote_perfective : ViewpointType.perfective.denote P = perfective P := by
  ext t; simp [ViewpointType.denote_iff, perfective_iff]

theorem denote_imperfective_iff :
    ViewpointType.imperfective.denote P t ↔ ∃ e, t < τ e ∧ P e := by
  simp [ViewpointType.denote_iff]

theorem denote_imperfective_le_unbounded :
    ViewpointType.imperfective.denote P ≤ unbounded P :=
  fun _ h ↦ let ⟨e, hlt, hP⟩ := denote_imperfective_iff.1 h; unbounded_iff.2 ⟨e, hlt.le, hP⟩

theorem perfective_mono : Monotone (perfective : (E → Prop) → NonemptyInterval T → Prop) :=
  inclusive_mono.comp runTimes_mono

theorem unbounded_mono : Monotone (unbounded : (E → Prop) → NonemptyInterval T → Prop) :=
  (diamond_mono _).comp runTimes_mono

/-- The perfective is closed under superintervals. -/
theorem monotone_perfective (P : E → Prop) : Monotone (perfective P) := monotone_inclusive _

/-- The non-strict imperfective is closed under subintervals. -/
theorem antitone_unbounded (P : E → Prop) : Antitone (unbounded P) :=
  fun _ _ hle h ↦ let ⟨e, he, hP⟩ := unbounded_iff.1 h; unbounded_iff.2 ⟨e, hle.trans he, hP⟩

theorem antitone_denote_imperfective (P : E → Prop) :
    Antitone (ViewpointType.imperfective.denote P) :=
  fun _ _ hle h ↦ let ⟨e, he, hP⟩ := denote_imperfective_iff.1 h
    denote_imperfective_iff.2 ⟨e, hle.trans_lt he, hP⟩

/-- The non-strict imperfective entails an interval property exactly when the run times entail
its durative reading. -/
theorem unbounded_le_iff : unbounded P ≤ q ↔ runTimes P ≤ durative q := by
  have h := diamond_box_gc (toSetRel (T := T) .le).inv (runTimes P) q
  rw [SetRel.inv_inv] at h
  rwa [durative, ← toSetRel_le]

/-- The perfective entails an interval property closed under superintervals exactly when the run
times do. -/
theorem perfective_le_iff (hq : Monotone q) : perfective P ≤ q ↔ runTimes P ≤ q :=
  ⟨(le_inclusive _).trans, fun h ↦ (inclusive_mono h).trans (inclusive_eq_of_monotone hq).le⟩

/-- Over the world of evaluation alone, the imperfective is the extensional one, the reference
interval within the run time of an actual event of the predicate. -/
@[simp] theorem imperfective_id (P : W → E → Prop) (w : W) :
    imperfective (fun _ ↦ SetRel.id) P w = unbounded (P w) := by
  ext t; simp [imperfective, box_id]

/-- Where the world of evaluation is accessible, the imperfective requires an actual event of the
predicate in progress. -/
theorem unbounded_of_imperfective {acc : NonemptyInterval T → SetRel W W} {P : W → E → Prop} {w : W}
    (hw : w ~[acc t] w) (h : imperfective acc P w t) : unbounded (P w) t :=
  h w hw

theorem imperfective_anti {acc acc' : NonemptyInterval T → SetRel W W} {P : W → E → Prop} {w : W}
    (h : acc t ⊆ acc' t) (ht : imperfective acc' P w t) : imperfective acc P w t :=
  fun v hv ↦ ht v (h hv)

/-- The perfective holds at a moment exactly when the moment is the run time of an event of the
predicate. -/
theorem perfective_pure_iff {a : T} : perfective P (.pure a) ↔ ∃ e, τ e = .pure a ∧ P e := by
  rw [perfective_iff]
  refine exists_congr fun e ↦ and_congr_left fun _ ↦ ⟨fun hle ↦ ?_, fun h ↦ h.le⟩
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hle
  exact NonemptyInterval.ext (Prod.ext (((τ e).fst_le_snd.trans h₂).antisymm h₁)
    (h₂.antisymm (h₁.trans (τ e).fst_le_snd)))

/-- The perfective holds throughout an interval exactly when every moment of it is the run time
of an event of the predicate. -/
theorem durative_perfective_iff :
    durative (perfective P) t ↔ ∀ a ∈ t, ∃ e, τ e = .pure a ∧ P e := by
  simp only [durative_iff_of_monotone (monotone_perfective P), perfective_pure_iff]

/-- Some subinterval of the reference interval lies within a run time exactly when a run time
overlaps the reference interval. -/
theorem inclusive_unbounded_iff : inclusive (unbounded P) t ↔ ∃ e, (τ e).Overlaps t ∧ P e := by
  rw [inclusive_iff]
  constructor
  · rintro ⟨j, hj, hu⟩
    obtain ⟨e, he, hP⟩ := unbounded_iff.1 hu
    obtain ⟨hj₁, hj₂⟩ := NonemptyInterval.le_def.1 hj
    obtain ⟨he₁, he₂⟩ := NonemptyInterval.le_def.1 he
    exact ⟨e, ⟨(he₁.trans j.fst_le_snd).trans hj₂, (hj₁.trans j.fst_le_snd).trans he₂⟩, hP⟩
  · rintro ⟨e, ⟨h₁, h₂⟩, hP⟩
    refine ⟨⟨(max (τ e).fst t.fst, min (τ e).snd t.snd), ?_⟩, ?_, unbounded_iff.2 ⟨e, ?_, hP⟩⟩
    · exact max_le (le_min (τ e).fst_le_snd h₁) (le_min h₂ t.fst_le_snd)
    · exact NonemptyInterval.le_def.2 ⟨le_max_right _ _, min_le_right _ _⟩
    · exact NonemptyInterval.le_def.2 ⟨le_max_left _ _, min_le_left _ _⟩

/-! ### Over the perfective -/

/-- The perfect of the perfective holds where an event of the predicate is over by the end of the
reference interval. -/
theorem perfect_perfective_iff : perfect (perfective P) t ↔ ∃ e, (τ e).snd ≤ t.snd ∧ P e := by
  rw [perfect_iff_of_monotone (monotone_perfective P)]
  exact ⟨fun ⟨_, h, hp⟩ ↦ let ⟨e, hle, hP⟩ := perfective_iff.1 hp
      ⟨e, (NonemptyInterval.le_def.1 hle).2.trans h, hP⟩,
    fun ⟨e, h, hP⟩ ↦ ⟨τ e, h, perfective_iff.2 ⟨e, le_rfl, hP⟩⟩⟩

/-- The prospective of the perfective holds where the reference interval precedes an event of the
predicate, Klein's prospective with the reference interval ending before the event starts. -/
theorem prospective_perfective_iff :
    prospective (perfective P) t ↔ ∃ e, t.Precedes (τ e) ∧ P e := by
  rw [prospective_iff]
  exact ⟨fun ⟨_, hj, hp⟩ ↦ let ⟨e, hle, hP⟩ := perfective_iff.1 hp
      ⟨e, hj.trans_le (NonemptyInterval.le_def.1 hle).1, hP⟩,
    fun ⟨e, hlt, hP⟩ ↦ ⟨τ e, hlt, perfective_iff.2 ⟨e, le_rfl, hP⟩⟩⟩

end Aspect
