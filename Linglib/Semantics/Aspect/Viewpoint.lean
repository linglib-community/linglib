module

public import Mathlib.Order.UpperLower.Closure
public import Linglib.Semantics.Aspect.Defs
public import Linglib.Semantics.Index
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
* `Aspect.prospective`: the prospective as an operator on interval properties, whose reference
  interval precedes the interval it introduces.
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
  `Aspect.perfect_eq_image`, `Aspect.prospective_eq_image`: the operators are images under Allen
  cells, so complex aspects compose by `Allen.comp`.
* `Aspect.mem_perfect_iff_of_isUpperSet`: for a property closed under superintervals, the perfect
  time span may end before the reference interval does.
* `Aspect.mem_perfect_prfv`, `Aspect.prospective_prfv`: over the perfective, the perfect holds
  where an event is over by the end of the reference interval and the prospective where the
  reference interval precedes one.
* `Aspect.mem_durative_iff_of_isUpperSet`, `Aspect.mem_durative_prfv`: a property closed under
  superintervals holds throughout a span when it holds at every moment of it, the perfective
  when every moment is the run time of an event.

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
* Event predicates range over any event domain with a temporal trace (`TemporalTrace`).
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

variable {T : Type*} [LinearOrder T] {W E : Type*} [TemporalTrace E T]

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

theorem isLowerSet_denote_imperfective (P : W → E → Prop) (w : W) :
    IsLowerSet (ViewpointType.imperfective.denote P w) :=
  fun _ _ hle ⟨e, hlt, hP⟩ ↦ ⟨e, hle.trans_lt hlt, hP⟩

theorem isUpperSet_prfv (P : W → E → Prop) (w : W) : IsUpperSet (PRFV P w) := by
  rw [prfv_eq_upperClosure]; exact (upperClosure _).upper

/-- The perfect, (22b), holds at the world-time points whose time is the right boundary, (22a),
of some perfect time span belonging to the interval property. -/
def PERF (p : W → Set (NonemptyInterval T)) : Set (Index W T) :=
  {s | ∃ pts ∈ p s.world, pts.snd = s.time}

variable {p q : W → Set (NonemptyInterval T)}

@[simp] theorem mem_perf {t : T} : ⟨w, t⟩ ∈ PERF p ↔ ∃ pts ∈ p w, pts.snd = t := Iff.rfl

/-- Under an adverbial fixing the left boundary in `D`, the perfect holds at `t` where the span
from a time of `D` to `t` belongs to the interval property. -/
theorem mem_perf_inter_preimage_fst {D : Set T} {t : T} :
    ⟨w, t⟩ ∈ PERF ((·.fst) ⁻¹' D ∩ p ·) ↔ ∃ x ∈ D, ∃ h : x ≤ t, ⟨(x, t), h⟩ ∈ p w := by
  rw [mem_perf]
  constructor
  · rintro ⟨⟨⟨x, s⟩, h⟩, ⟨hx, hp⟩, rfl⟩
    exact ⟨x, hx, h, hp⟩
  · rintro ⟨x, hx, h, hp⟩
    exact ⟨⟨(x, t), h⟩, ⟨hx, hp⟩, rfl⟩

theorem perf_mono (h : ∀ w, p w ⊆ q w) : PERF p ⊆ PERF q :=
  fun _ ⟨pts, hp, hRB⟩ ↦ ⟨pts, h _ hp, hRB⟩

/-- `atPoint p` holds at the world-time points whose degenerate interval belongs to `p`, as the
non-perfect forms are evaluated. -/
def atPoint (p : W → Set (NonemptyInterval T)) : Set (Index W T) :=
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

/-- For an interval property closed under superintervals, the perfect holds where some span
belonging to the property is over by the end of the reference interval: the span need not end
with the reference interval, since it extends to one that does. -/
theorem mem_perfect_iff_of_isUpperSet (hp : IsUpperSet (p w)) :
    t ∈ perfect p w ↔ ∃ pts ∈ p w, pts.snd ≤ t.snd := by
  constructor
  · rintro ⟨pts, hpts, -, hsnd⟩
    exact ⟨pts, hpts, hsnd.ge⟩
  · rintro ⟨pts, hpts, hle⟩
    exact ⟨⟨(pts.fst ⊓ t.fst, t.snd), inf_le_right.trans t.fst_le_snd⟩,
      hp (NonemptyInterval.le_def.2 ⟨inf_le_left, hle⟩) hpts, inf_le_right, rfl⟩

/-- For an interval property closed under superintervals, the perfect is its image under the
converse of ending no later: a perfect time span is a nonfuture reference time. -/
theorem perfect_eq_image_inv_endsNoLater (hp : IsUpperSet (p w)) :
    perfect p w = (Allen.toSetRel (Allen.inv Allen.endsNoLater)).image (p w) := by
  ext i
  simp [SetRel.image, mem_perfect_iff_of_isUpperSet hp]

/-- The perfect of the perfective holds where an event of the predicate is over by the end of the
reference interval. -/
theorem mem_perfect_prfv : t ∈ perfect (PRFV P) w ↔ ∃ e : E, (τ e).snd ≤ t.snd ∧ P w e := by
  rw [mem_perfect_iff_of_isUpperSet (isUpperSet_prfv P w)]
  exact ⟨fun ⟨_, ⟨e, hle, hP⟩, h⟩ ↦ ⟨e, (NonemptyInterval.le_def.1 hle).2.trans h, hP⟩,
    fun ⟨e, h, hP⟩ ↦ ⟨τ e, ⟨e, le_rfl, hP⟩, h⟩⟩

/-- `prospective p` holds at a reference interval that precedes some interval belonging to `p`,
the prospective as an operator on interval properties. -/
def prospective (p : W → Set (NonemptyInterval T)) : W → Set (NonemptyInterval T) :=
  fun w ↦ {i | ∃ j ∈ p w, i.Precedes j}

@[simp] theorem mem_prospective : t ∈ prospective p w ↔ ∃ j ∈ p w, t.Precedes j := Iff.rfl

/-- The prospective is the image of the interval property under the cell of precedence, the
converse of the cell along which the quantificational past looks back. -/
theorem prospective_eq_image (p : W → Set (NonemptyInterval T)) (w : W) :
    prospective p w = (Allen.toSetRel Allen.precedes).image (p w) := by
  ext i
  simp [prospective, SetRel.image]

theorem prospective_mono (h : ∀ w, p w ⊆ q w) (w : W) : prospective p w ⊆ prospective q w :=
  fun _ ⟨j, hp, hj⟩ ↦ ⟨j, h w hp, hj⟩

/-- A reference interval within one that precedes an interval precedes it too. -/
theorem isLowerSet_prospective (p : W → Set (NonemptyInterval T)) (w : W) :
    IsLowerSet (prospective p w) :=
  fun _ _ hle ⟨j, hp, hj⟩ ↦ ⟨j, hp, (NonemptyInterval.le_def.1 hle).2.trans_lt hj⟩

/-- The prospective of the perfective holds where the reference interval precedes an event of the
predicate, Klein's prospective with the reference interval ending before the event starts. -/
theorem prospective_prfv (P : W → E → Prop) (w : W) :
    prospective (PRFV P) w = ofRel NonemptyInterval.Precedes P w :=
  Set.ext fun _ ↦
    ⟨fun ⟨_, ⟨e, hle, hP⟩, hj⟩ ↦ ⟨e, hj.trans_le (NonemptyInterval.le_def.1 hle).1, hP⟩,
      fun ⟨e, hlt, hP⟩ ↦ ⟨τ e, ⟨e, le_rfl, hP⟩, hlt⟩⟩

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

/-- An interval property closed under superintervals holds throughout a span exactly when it
holds at every moment of the span. -/
theorem mem_durative_iff_of_isUpperSet (hp : IsUpperSet (p w)) :
    t ∈ durative p w ↔ ∀ a ∈ t, .pure a ∈ p w := by
  refine ⟨fun h _ ha ↦ h (show _ ≤ t from NonemptyInterval.le_def.2 ha), fun h j hj ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hj
  exact hp (show .pure j.fst ≤ j from NonemptyInterval.le_def.2 ⟨le_rfl, j.fst_le_snd⟩)
    (h j.fst ⟨h₁, j.fst_le_snd.trans h₂⟩)

/-- The perfective holds at a moment exactly when the moment is the run time of an event of the
predicate. -/
theorem pure_mem_prfv {a : T} : .pure a ∈ PRFV P w ↔ ∃ e : E, τ e = .pure a ∧ P w e := by
  refine exists_congr fun e ↦ and_congr_left fun _ ↦ ⟨fun hle ↦ ?_, fun h ↦ h.le⟩
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hle
  exact NonemptyInterval.ext (Prod.ext (((τ e).fst_le_snd.trans h₂).antisymm h₁)
    (h₂.antisymm (h₁.trans (τ e).fst_le_snd)))

/-- The perfective holds throughout a span exactly when every moment of the span is the run time
of an event of the predicate. -/
theorem mem_durative_prfv :
    t ∈ durative (PRFV P) w ↔ ∀ a ∈ t, ∃ e : E, τ e = .pure a ∧ P w e := by
  simp only [mem_durative_iff_of_isUpperSet (isUpperSet_prfv P w), pure_mem_prfv]

end Aspect
