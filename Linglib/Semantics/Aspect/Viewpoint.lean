module

public import Mathlib.Order.UpperLower.Closure
public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.Reference.Context.Index
public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Events.Basic
public import Linglib.Semantics.Tense.Allen

/-!
# Viewpoint aspect

This file defines viewpoint aspect, which in Smith's theory, following Klein, relates the topic
time to the situation time. A relation between the reference time and the run time of an event
gives an operator from event predicates to interval properties, at each world a set of reference
intervals, and the operator of a viewpoint is that of its relation; the perfective of Knick and
Sharf is an instance. The imperfective is modal: the reference interval lies
within the run time of an event of the predicate in every world of a modal domain fixed by the
world of evaluation and the reference interval, so that an event in progress need never be
completed. Over the domain of the world of evaluation alone it is the extensional imperfective.
The perfect takes an interval property to a set of world-time points through a perfect time span,
which a perfect-level adverbial in the sense of Iatridou, Anagnostopoulou and Izvorski restricts.
An interval adverbial is read durative, the predicate holding at every subinterval of its interval,
or inclusive, at some subinterval, as Dowty, Mittwoch and Vlach distinguish them.

## Main definitions

* `Aspect.ViewpointType.cell`: the cell of Allen relations a viewpoint imposes between the topic
  time and the situation time.
* `Aspect.ofRel`: the operator of a relation between reference time and run time, and
  `Aspect.modalOfRel` the operator of a relation over a modal domain.
* `Aspect.IMPF`: the imperfective.
* `Aspect.PRFV`: the perfective.
* `Aspect.UNBOUNDED`: Pancheva's non-strict imperfective.
* `Aspect.perfect`: the perfect as an operator on interval properties, whose reference interval
  is a final subinterval of the perfect time span; `Aspect.PERF` is its value at a point.
* `Aspect.durative`, `Aspect.inclusive`: the durative and inclusive readings of an interval
  adverbial.

## Main results

* `Aspect.prfv_eq_upperClosure`: the perfective holds on the upper closure of the predicate's
  run times.
* `Aspect.unbounded_eq_lowerClosure`: the non-strict imperfective holds on their lower closure.
* `Aspect.inclusive_eq_upperClosure`: the inclusive reading is the upper closure.
* `Aspect.impf_singleton`: over the world of evaluation alone, the imperfective is the
  extensional one.
* `Aspect.ViewpointType.denote_eq_image`, `Aspect.unbounded_eq_image`,
  `Aspect.perfect_eq_image`: the operators are images under Allen cells, so complex aspects
  compose by `Allen.comp`.

## Implementation notes

* Of Klein's relations, TT INCL TSit is the imperfective, TT AT TSit the perfective, TT AFTER
  TSit the perfect and TT BEFORE TSit the prospective. Knick and Sharf's imperfective, (25),
  includes the reference time properly, `ViewpointType.imperfective.denote`; the modal imperfective
  includes it, as Kratzer's and Ferreira's do.
* The modal domain of the imperfective is a set of worlds for each world and reference interval:
  Ferreira's best worlds of a circumstantial base, Deo's inertia histories, or the language-specific
  modal bases of Arregui, Rivero and Salanova.
* Smith's neutral viewpoint includes the initial point of the situation and at least one internal
  stage where the situation has stages: the topic time contains the start of the situation and,
  when the situation is not instantaneous, reaches past it.
* The operators follow Knick and Sharf's equations, with a boundary a time point where the
  paper has a final or initial subinterval. The predicate applies to the outer reference time,
  which beneath the perfect is the perfect time span.
* A perfect-level adverbial is a set of spans, which the perfect intersects with the interval
  property, `PERF (adv ∩ p ·)`: *since t₀* admits the spans starting at `t₀`, Knick and Sharf's
  domain restriction `tᵣ` the spans starting in `tᵣ`, and the covert adverbial of an unmodified
  perfect every span.
* Event predicates range over any event domain with a temporal trace (`Event.TemporalTrace`).
* An interval property is a family of sets of intervals indexed by worlds,
  `W → Set (NonemptyInterval T)`, so that mathlib's order closures and lower and upper sets apply
  to it directly; the perfect yields a set of world-time points.

## References

* [smith-1997]
* [klein-1994]
* [ferreira-2016]
* [deo-2009]
* [arregui-rivero-salanova-2014]
* [knick-sharf-2026]
* [pancheva-2003]
* [iatridou-anagnostopoulou-izvorski-2001]
* [dowty-1979]
* [mittwoch-1988]
* [vlach-1993]
-/

@[expose] public section

namespace Aspect

/-- `v.ttTSitRelation tt tsit` is the relation the viewpoint `v` imposes between the topic time and
the situation time, which is inclusion in the situation, containment of the situation,
posteriority, anteriority, and, for the neutral viewpoint, containment of the situation's
start and of a stage after it. -/
def ViewpointType.ttTSitRelation {T : Type*} [LinearOrder T]
    (v : ViewpointType) (tt tsit : NonemptyInterval T) : Prop :=
  match v with
  | .imperfective => tt < tsit
  | .perfective => tsit ≤ tt
  | .perfect => tsit.snd ≤ tt.fst
  | .prospective => tt.snd ≤ tsit.fst
  | .neutral => tsit.fst ∈ tt ∧ (tsit.fst < tsit.snd → tsit.fst < tt.snd)

instance {T : Type*} [LinearOrder T] (v : ViewpointType) (tt tsit : NonemptyInterval T) :
    Decidable (v.ttTSitRelation tt tsit) := by
  cases v <;> unfold ViewpointType.ttTSitRelation <;> infer_instance

/-- The cell of the viewpoint's relation, the topic time first: within the situation, around it,
after it or from its end, before it or up to its start, and around its start and a stage after
it. -/
def ViewpointType.cell : ViewpointType → Finset Allen.Relation
  | .imperfective => Allen.lt
  | .perfective => Allen.inv Allen.le
  | .perfect => Allen.inv Allen.isBefore
  | .prospective => Allen.isBefore
  | .neutral => (Allen.inv Allen.startsWithin).filter fun r ↦ r.secondShape = .lt → r.sndFst = .gt

theorem ViewpointType.ttTSitRelation_iff {T : Type*} [LinearOrder T] (v : ViewpointType)
    (tt tsit : NonemptyInterval T) :
    v.ttTSitRelation tt tsit ↔ (tsit, tt) ∈ Allen.toSetRel v.cell := by
  cases v <;> simp [ttTSitRelation, cell, Allen.ofEndpoints, compare_lt_iff_lt, compare_gt_iff_gt]

/-! ### Operators -/

open Event (τ)

variable {T : Type*} [LinearOrder T] {W E : Type*} [Event.TemporalTrace E T]

/-- The aspect operator of a relation `R` gives, at each world, the reference intervals that
stand in `R` to the run time of some event of the predicate. -/
def ofRel (R : NonemptyInterval T → NonemptyInterval T → Prop) (P : W → E → Prop) :
    W → Set (NonemptyInterval T) :=
  fun w ↦ {t | ∃ e : E, R t (τ e) ∧ P w e}

variable {P : W → E → Prop} {w : W} {t : NonemptyInterval T}

@[simp] theorem mem_ofRel {R : NonemptyInterval T → NonemptyInterval T → Prop} :
    t ∈ ofRel R P w ↔ ∃ e : E, R t (τ e) ∧ P w e := Iff.rfl

theorem ofRel_mono {R S : NonemptyInterval T → NonemptyInterval T → Prop}
    (h : ∀ t s, R t s → S t s) (P : W → E → Prop) (w : W) : ofRel R P w ⊆ ofRel S P w :=
  fun _ ⟨e, hR, hP⟩ ↦ ⟨e, h _ _ hR, hP⟩

/-- The aspect operator of a relation `R` over a modal domain `acc` gives, at each world `w`, the
reference intervals `t` that stand in `R` to the run time of some event of the predicate in every
world of `acc w t`. -/
def modalOfRel (acc : W → NonemptyInterval T → Set W)
    (R : NonemptyInterval T → NonemptyInterval T → Prop) (P : W → E → Prop) :
    W → Set (NonemptyInterval T) :=
  fun w ↦ {t | ∀ v ∈ acc w t, t ∈ ofRel R P v}

section ModalOfRel

variable {acc acc' : W → NonemptyInterval T → Set W}
  {R : NonemptyInterval T → NonemptyInterval T → Prop}

@[simp] theorem mem_modalOfRel :
    t ∈ modalOfRel acc R P w ↔ ∀ v ∈ acc w t, ∃ e : E, R t (τ e) ∧ P v e := Iff.rfl

/-- Over the domain of the world of evaluation alone, the operator of a relation is extensional. -/
@[simp] theorem modalOfRel_singleton (R : NonemptyInterval T → NonemptyInterval T → Prop)
    (P : W → E → Prop) : modalOfRel (fun w _ ↦ {w}) R P = ofRel R P := by
  ext w t
  simp [modalOfRel]

theorem modalOfRel_anti (h : ∀ w t, acc w t ⊆ acc' w t) :
    modalOfRel acc' R P w ⊆ modalOfRel acc R P w :=
  fun t ht v hv ↦ ht v (h w t hv)

theorem mem_ofRel_of_mem_modalOfRel (hw : w ∈ acc w t) (h : t ∈ modalOfRel acc R P w) :
    t ∈ ofRel R P w :=
  h w hw

end ModalOfRel

/-- The operator of a viewpoint is the operator of its relation between the topic time and the
situation time. -/
def ViewpointType.denote (v : ViewpointType) (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  ofRel v.ttTSitRelation P

/-- The perfective, (28), holds where the run time of an event of the predicate is contained in
the reference time. -/
def PRFV (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  ViewpointType.perfective.denote P

/-- The prospective holds where the reference time precedes an event of the predicate. -/
def PROSP (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  ViewpointType.prospective.denote P

/-- The non-strict imperfective, (7b) of [pancheva-2003], holds where the reference time is
contained, not necessarily properly, in the run time of an event of the predicate. -/
def UNBOUNDED (P : W → E → Prop) : W → Set (NonemptyInterval T) :=
  ofRel (· ≤ ·) P

/-- The imperfective holds at a reference interval when, in every world of the modal domain
`acc w t`, the interval lies within the run time of an event of the predicate. The event need not
be actual, so an event in progress need never be completed. -/
def IMPF (acc : W → NonemptyInterval T → Set W) (P : W → E → Prop) :
    W → Set (NonemptyInterval T) :=
  modalOfRel acc (· ≤ ·) P

theorem mem_impf {acc : W → NonemptyInterval T → Set W} :
    t ∈ IMPF acc P w ↔ ∀ v ∈ acc w t, ∃ e : E, t ≤ τ e ∧ P v e := Iff.rfl

theorem mem_denote_imperfective :
    t ∈ ViewpointType.imperfective.denote P w ↔ ∃ e : E, t < τ e ∧ P w e := Iff.rfl

theorem mem_prfv : t ∈ PRFV P w ↔ ∃ e : E, τ e ≤ t ∧ P w e := Iff.rfl

theorem mem_prosp : t ∈ PROSP P w ↔ ∃ e : E, t.snd ≤ (τ e).fst ∧ P w e := Iff.rfl

theorem mem_unbounded : t ∈ UNBOUNDED P w ↔ ∃ e : E, t ≤ τ e ∧ P w e := Iff.rfl

/-- The operator of a viewpoint is the image of the predicate's run times under the viewpoint's
cell. -/
theorem ViewpointType.denote_eq_image (v : ViewpointType) (P : W → E → Prop) (w : W) :
    v.denote P w = (Allen.toSetRel v.cell).image (τ '' {e | P w e}) := by
  ext t
  simp [ViewpointType.denote, ofRel, SetRel.image, ViewpointType.ttTSitRelation_iff, and_comm]

theorem unbounded_eq_image (P : W → E → Prop) (w : W) :
    UNBOUNDED P w = (Allen.toSetRel Allen.le).image (τ '' {e | P w e}) := by
  ext t
  simp [UNBOUNDED, ofRel, SetRel.image, and_comm]

/-- Over the world of evaluation alone, the imperfective is the extensional one, the reference
interval within the run time of an actual event of the predicate. -/
@[simp] theorem impf_singleton (P : W → E → Prop) : IMPF (fun w _ ↦ {w}) P = UNBOUNDED P :=
  modalOfRel_singleton _ P

/-- Where the modal domain contains the world of evaluation, the imperfective requires an actual
event of the predicate in progress. -/
theorem mem_unbounded_of_mem_impf {acc : W → NonemptyInterval T → Set W} (hw : w ∈ acc w t)
    (h : t ∈ IMPF acc P w) : t ∈ UNBOUNDED P w :=
  mem_ofRel_of_mem_modalOfRel hw h

theorem denote_imperfective_subset_unbounded (P : W → E → Prop) (w : W) :
    ViewpointType.imperfective.denote P w ⊆ UNBOUNDED P w :=
  ofRel_mono (R := (· < ·)) (S := (· ≤ ·)) (fun _ _ ↦ le_of_lt) P w

/-- The non-strict imperfective holds on the lower closure of the predicate's run times. -/
theorem unbounded_eq_lowerClosure : UNBOUNDED P w = lowerClosure (τ '' {e | P w e}) :=
  Set.ext fun _ ↦ ⟨fun ⟨e, hle, hP⟩ ↦ ⟨τ e, Set.mem_image_of_mem τ hP, hle⟩,
    fun ⟨_, ⟨e, hP, rfl⟩, hle⟩ ↦ ⟨e, hle, hP⟩⟩

/-- The perfective holds on the upper closure of the predicate's run times. -/
theorem prfv_eq_upperClosure : PRFV P w = upperClosure (τ '' {e | P w e}) :=
  Set.ext fun _ ↦ ⟨fun ⟨e, hle, hP⟩ ↦ ⟨τ e, Set.mem_image_of_mem τ hP, hle⟩,
    fun ⟨_, ⟨e, hP, rfl⟩, hle⟩ ↦ ⟨e, hle, hP⟩⟩

theorem isLowerSet_unbounded (P : W → E → Prop) (w : W) : IsLowerSet (UNBOUNDED P w) := by
  rw [unbounded_eq_lowerClosure]; exact (lowerClosure _).lower

theorem isUpperSet_prfv (P : W → E → Prop) (w : W) : IsUpperSet (PRFV P w) := by
  rw [prfv_eq_upperClosure]; exact (upperClosure _).upper

/-- The perfect, (22b), holds at the world-time points whose time is the right boundary, (22a),
of some perfect time span belonging to the interval property. -/
def PERF (p : W → Set (NonemptyInterval T)) : Set (Kaplan.Index W T) :=
  {s | ∃ pts ∈ p s.world, pts.snd = s.time}

variable {p q : W → Set (NonemptyInterval T)}

@[simp] theorem mem_perf {t : T} : (w, t) ∈ PERF p ↔ ∃ pts ∈ p w, pts.snd = t := Iff.rfl

theorem perf_mono (h : ∀ w, p w ⊆ q w) : PERF p ⊆ PERF q :=
  fun _ ⟨pts, hp, hRB⟩ ↦ ⟨pts, h _ hp, hRB⟩

/-- `atPoint p` holds at the world-time points whose degenerate interval belongs to `p`, as the
non-perfect forms are evaluated. -/
def atPoint (p : W → Set (NonemptyInterval T)) : Set (Kaplan.Index W T) :=
  {s | NonemptyInterval.pure s.time ∈ p s.world}

/-- `perfect p` holds at a reference interval that is a final subinterval of some perfect time
span belonging to `p`, the perfect as an operator on interval properties. -/
def perfect (p : W → Set (NonemptyInterval T)) : W → Set (NonemptyInterval T) :=
  fun w ↦ {i | ∃ pts ∈ p w, i.FinalSubinterval pts}

theorem perf_eq_atPoint_perfect (p : W → Set (NonemptyInterval T)) :
    PERF p = atPoint (perfect p) := by
  refine Set.ext fun s ↦ exists_congr fun pts ↦ and_congr_right fun _ ↦ ?_
  change pts.snd = s.time ↔ pts.fst ≤ s.time ∧ s.time = pts.snd
  exact ⟨fun h ↦ ⟨h ▸ pts.fst_le_snd, h.symm⟩, fun h ↦ h.2.symm⟩

/-- The perfect is the image of the perfect time spans under the final-subinterval cell, so the
perfect of a viewpoint relates its reference interval to the run time as the composite of the
two cells does (`Allen.image_toSetRel_subset_comp`). -/
theorem perfect_eq_image (p : W → Set (NonemptyInterval T)) (w : W) :
    perfect p w = (Allen.toSetRel Allen.finalSubinterval).image (p w) := by
  ext i
  simp [perfect, SetRel.image]

theorem perfect_mono (h : ∀ w, p w ⊆ q w) (w : W) : perfect p w ⊆ perfect q w :=
  fun _ ⟨pts, hp, hf⟩ ↦ ⟨pts, h w hp, hf⟩

/-! ### Durative and inclusive readings -/

/-- `durative p` holds at a span when `p` holds at every subinterval of it, the durative reading
of an interval adverbial, *throughout*. -/
def durative (p : W → Set (NonemptyInterval T)) : W → Set (NonemptyInterval T) :=
  fun w ↦ {i | Set.Iic i ⊆ p w}

/-- `inclusive p` holds at a span when `p` holds at some subinterval of it, the inclusive reading
of an interval adverbial, *in*. -/
def inclusive (p : W → Set (NonemptyInterval T)) : W → Set (NonemptyInterval T) :=
  fun w ↦ {i | ∃ j ∈ p w, j ≤ i}

/-- The inclusive reading is the upper closure of the interval property. -/
theorem inclusive_eq_upperClosure : inclusive p w = upperClosure (p w) :=
  rfl

theorem inclusive_eq_of_isUpperSet (hp : IsUpperSet (p w)) : inclusive p w = p w :=
  hp.upperClosure

theorem durative_subset_inclusive : durative p w ⊆ inclusive p w :=
  fun i h ↦ ⟨i, h (Set.mem_Iic.2 le_rfl), le_rfl⟩

end Aspect
