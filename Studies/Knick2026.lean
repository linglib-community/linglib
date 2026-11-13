module

public import Linglib.Data.Examples.Knick2026
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Aspect.SubintervalProperty
public import Linglib.Semantics.Conditionals.SelectionFunction

/-!
# Knick (2026): Future shifting with present marking in Khalkha Mongolian

Knick argues that Khalkha *-nA*, described as a non-past, is a present tense. With one conjoined
subject's eventuality at the utterance time and the other's after it, a non-past sentence is true
and [the present is not](##nonPast_and_not_present_of_split), and a non-past perfect is [true of
an event at any time](##nonPast_perfect_prfv). The bare verb is perfective, and the present
perfective holds only where [every moment is the run time of an
eventuality](##mem_present_prfv), as with a state. The future is a silent modal over a silent
prospective, [an eventuality to come](##mem_present_future_iff); the modal selects a world and so
[commutes with negation](##MOD_compl). Aktionsart thus [predicts the readings](##available_rows).

## Implementation notes

* A sentence is the set of worlds in which it holds at the utterance time, an interval. The rule
  that a simple present sentence hold at every part of the utterance time is built into the
  present tense. It is [idle on a property closed under subintervals](##present_eq_of_isLowerSet),
  the future structure and the negated present perfective among them; under it the negated future
  [excludes an eventuality that starts within the utterance time](##mem_present_compl_future_iff),
  which the future does not include.
* The non-past quantifies over reference times no part of which precedes the utterance time,
  those standing to it in `Allen.startsNoEarlier`, [the mirror image](##mem_nonPast_iff_dual) of
  the nonfuture reference times of [matthewson-2006].
* The perfect is the library's, whose span ends with the reference interval, where the paper's
  may end before it; over the perfective the two agree
  (`Aspect.mem_perfect_iff_of_isUpperSet`).
* A subject's eventualities are those of its predicate, and a distributive reading of conjoined
  subjects places an eventuality of each within the reference time.
* A universal modal over a realistic base commutes with negation [only when the base is
  trivial](##box_compl_eq_iff_of_isRefl), which is why the paper's first modal gives way to the
  selectional one.
* The modal base at a reference time is a relation between worlds, the base of a world its
  successors. A circumstantial base is realistic, the relation reflexive, as historical
  alternatives are (`Temporal.TWFrame.alt`); selection from it returns the world of evaluation, so
  [the modal is the identity](##MOD_eq).
* Negation is interpreted where the paper's structure for the negated future has it, above the
  modal and the prospective. Beneath the prospective it would negate the perfective at some
  future time within the salient interval, which
  [the affirmative leaves open](##exists_prospective_compl_prfv).
* A stative predicate is one with the subinterval property and an eventive predicate one whose
  events take time; achievements, which are instantaneous, fail the present perfective
  [by not recurring at every moment](##not_mem_present_prfv_of_subsingleton).

## TODO

* The restriction of the prospective to the perfective is the paper's stipulation; the
  present-only readings of the perfect and the imperfective are not derived.
* The morphosyntax of the negator *-güi*, the diagnostics for the modality of *-kh* and modal
  subordination are left in prose.

## References

* [knick-2026]
* [ogihara-2007]
* [bennett-partee-1972]
* [matthewson-2006]
* [cariani-santorio-2018]
-/

@[expose] public section

namespace Knick2026

open Aspect Conditional ModalLogic Set
open Event (τ)
open scoped SetRel

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] {P Q : W → E → Prop}
  {p : W → Set (NonemptyInterval T)} {u g : NonemptyInterval T} {w : W}

/-! ### The present and the non-past -/

/-- (4) under the rule (28): the present holds where the property holds at every part of the
utterance time `u`. -/
def present (u : NonemptyInterval T) (p : W → Set (NonemptyInterval T)) : Set W :=
  {w | u ∈ durative p w}

theorem present_subset : present u p ⊆ {w | u ∈ p w} := fun _ h ↦ h (mem_Iic.2 le_rfl)

theorem present_eq_of_isLowerSet (h : ∀ w, IsLowerSet (p w)) : present u p = {w | u ∈ p w} :=
  Set.ext fun w ↦ by rw [present, mem_ofPred_eq, durative_eq_of_isLowerSet (h w), mem_ofPred_eq]

/-- (20): the non-past holds where the property holds of a reference time no part of which
precedes the utterance time `u`. -/
def nonPast (u : NonemptyInterval T) (p : W → Set (NonemptyInterval T)) : Set W :=
  {w | ∃ t ∈ p w, ∀ j ≤ t, ¬ j.Precedes u}

theorem mem_nonPast : w ∈ nonPast u p ↔ ∃ t ∈ p w, u.fst ≤ t.fst := by
  simp only [nonPast, mem_ofPred_eq, NonemptyInterval.forall_le_not_precedes_iff]

-- (20): the non-past is the nonfuture tense of [matthewson-2006] on reversed time
theorem mem_nonPast_iff_dual : w ∈ nonPast u p ↔
    ∃ t ∈ p w, (u.dual, t.dual) ∈ Allen.toSetRel Allen.endsNoLater := by
  simp [mem_nonPast]

theorem nonPast_prfv : nonPast u (PRFV P) = {w | ∃ e, u.fst ≤ (τ e).fst ∧ P w e} := by
  ext w
  rw [mem_nonPast]
  exact ⟨fun ⟨_, ⟨e, hle, hP⟩, h⟩ ↦ ⟨e, h.trans (NonemptyInterval.le_def.1 hle).1, hP⟩,
    fun ⟨e, h, hP⟩ ↦ ⟨τ e, ⟨e, le_rfl, hP⟩, h⟩⟩

-- a non-past reference time spans the eventualities of both subjects
theorem nonPast_prfv_inter :
    nonPast u (fun v ↦ PRFV P v ∩ PRFV Q v) = nonPast u (PRFV P) ∩ nonPast u (PRFV Q) := by
  ext w
  simp only [nonPast_prfv, mem_inter_iff, mem_ofPred_eq, mem_nonPast]
  constructor
  · rintro ⟨t, ⟨⟨e₁, h₁, hP⟩, e₂, h₂, hQ⟩, h⟩
    exact ⟨⟨e₁, h.trans (NonemptyInterval.le_def.1 h₁).1, hP⟩,
      e₂, h.trans (NonemptyInterval.le_def.1 h₂).1, hQ⟩
  · rintro ⟨⟨e₁, h₁, hP⟩, e₂, h₂, hQ⟩
    exact ⟨τ e₁ ⊔ τ e₂, ⟨⟨e₁, le_sup_left, hP⟩, e₂, le_sup_right, hQ⟩, le_inf h₁ h₂⟩

theorem not_mem_prfv_of_forall_precedes (h : ∀ e, Q w e → u.Precedes (τ e)) : u ∉ PRFV Q w :=
  fun ⟨e, hle, hQ⟩ ↦ (((τ e).fst_le_snd.trans (NonemptyInterval.le_def.1 hle).2).not_gt (h e hQ))

/-- The non-past perfect of a perfective is true of an event at any time, one wholly in the
future included (24), where the present perfect requires
[an event over by the utterance time](##Aspect.mem_perfect_prfv). -/
theorem nonPast_perfect_prfv : nonPast u (perfect (PRFV P)) = {w | ∃ e, P w e} := by
  ext w
  rw [mem_nonPast]
  exact ⟨fun ⟨_, ⟨_, ⟨e, _, hP⟩, _⟩, _⟩ ↦ ⟨e, hP⟩, fun ⟨e, hP⟩ ↦
    ⟨.pure ((τ e).snd ⊔ u.fst), mem_perfect_prfv.2 ⟨e, le_sup_left, hP⟩, le_sup_right⟩⟩

-- (13): the present perfect is false when the events all lie ahead
theorem not_mem_present_perfect_prfv (h : ∀ e, P w e → u.Precedes (τ e)) :
    w ∉ present u (perfect (PRFV P)) := fun hu ↦
  let ⟨e, hle, hP⟩ := mem_perfect_prfv.1 (present_subset hu)
  (((τ e).fst_le_snd.trans hle).not_gt (h e hP))

/-! ### The present perfective -/

-- (35b): every moment of the utterance time is the run time of an eventuality
theorem mem_present_prfv : w ∈ present u (PRFV P) ↔ ∀ a ∈ u, ∃ e, τ e = .pure a ∧ P w e :=
  mem_durative_prfv

-- at an instant an instantaneous eventuality suffices, as for [bennett-partee-1972]
theorem mem_present_pure_prfv {a : T} :
    w ∈ present (.pure a) (PRFV P) ↔ ∃ e, τ e = .pure a ∧ P w e := by
  simp [mem_present_prfv, NonemptyInterval.mem_pure]

-- the rule (28) is the pointwise condition at every moment of the utterance time
theorem mem_present_iff_of_isUpperSet (h : IsUpperSet (p w)) :
    w ∈ present u p ↔ ∀ a ∈ u, w ∈ present (.pure a) p := by
  simp only [present, mem_ofPred_eq, mem_durative_iff_of_isUpperSet h, NonemptyInterval.mem_pure,
    forall_eq]

-- (41b)
theorem not_mem_present_prfv_of_forall_lt (h : ∀ e, P w e → (τ e).fst < (τ e).snd) :
    w ∉ present u (PRFV P) := fun hw ↦
  let ⟨e, he, hP⟩ := mem_present_prfv.1 hw u.fst ⟨le_rfl, u.fst_le_snd⟩
  lt_irrefl u.fst (by simpa [he] using h e hP)

-- (46a)
theorem not_mem_present_prfv_of_subsingleton (hu : u.fst < u.snd)
    (h : ∀ e e', P w e → P w e' → τ e = τ e') : w ∉ present u (PRFV P) := fun hw ↦ by
  obtain ⟨e, he, hP⟩ := mem_present_prfv.1 hw u.fst ⟨le_rfl, u.fst_le_snd⟩
  obtain ⟨e', he', hP'⟩ := mem_present_prfv.1 hw u.snd ⟨u.fst_le_snd, le_rfl⟩
  exact hu.ne (by simpa [he, he'] using congrArg (·.fst) (h e e' hP hP'))

-- (48b), (51)
theorem mem_present_prfv_of_unbounded (h : HasSubintervalProperty P) (hu : u ∈ UNBOUNDED P w) :
    w ∈ present u (PRFV P) :=
  h.unbounded_subset_durative_prfv w hu

/-! ### The modal -/

-- the universal modal (37) over a realistic base is scopeless only over a trivial base
theorem box_compl_eq_iff_of_isRefl {R : SetRel W W} [R.IsRefl] :
    (∀ p : W → Prop, □[R] pᶜ = (□[R] p)ᶜ) ↔ R = SetRel.id := by
  rw [box_compl_eq_iff]
  constructor
  · rintro ⟨f, rfl⟩
    have hf : f = id := funext fun w ↦ SetRel.rfl (R := Function.graph f) (a := w)
    subst hf
    ext ⟨a, b⟩
    exact Iff.rfl
  · rintro rfl
    exact ⟨id, Set.ext fun ⟨a, b⟩ ↦ Iff.rfl⟩

variable (s : SelectionFunction W) (R : NonemptyInterval T → SetRel W W)

/-- (71): the modal holds at a reference time where the property holds at the world selected
from the modal base `R` at that time. -/
def MOD (p : W → Set (NonemptyInterval T)) : W → Set (NonemptyInterval T) :=
  fun w ↦ {t | w ∈ s.modal (R t) {v | t ∈ p v}}

/-- Negation above the modal is negation beneath it (69), (72). -/
theorem MOD_compl (p : W → Set (NonemptyInterval T)) :
    MOD s R (fun v ↦ (p v)ᶜ) = fun v ↦ (MOD s R p v)ᶜ :=
  rfl

variable {s R}

theorem MOD_eq [∀ t, (R t).IsRefl] (p : W → Set (NonemptyInterval T)) : MOD s R p = p := by
  ext w t
  rw [MOD, mem_ofPred_eq, SelectionFunction.modal_eq_id]
  rfl

/-! ### The future -/

variable (s R) in
/-- (35a): the future structure beneath the present, the modal over the prospective (38), which
introduces a time after the reference time and within the salient interval `g`. -/
def future (g : NonemptyInterval T) (p : W → Set (NonemptyInterval T)) :
    W → Set (NonemptyInterval T) :=
  MOD s R (prospective fun v ↦ Iic g ∩ p v)

theorem mem_prospective_Iic_prfv : u ∈ prospective (fun v ↦ Iic g ∩ PRFV P v) w ↔
    ∃ e, τ e ≤ g ∧ u.Precedes (τ e) ∧ P w e :=
  ⟨fun ⟨_, ⟨hg, e, hle, hP⟩, hj⟩ ↦
      ⟨e, hle.trans hg, hj.trans_le (NonemptyInterval.le_def.1 hle).1, hP⟩,
    fun ⟨e, hg, hlt, hP⟩ ↦ ⟨τ e, ⟨hg, e, le_rfl, hP⟩, hlt⟩⟩

variable [∀ t, (R t).IsRefl]

/-- Over a realistic base the future holds where an eventuality of the predicate lies within the
salient interval after the utterance time (42); the rule (28) is idle on it. -/
theorem mem_present_future_iff : w ∈ present u (future s R g (PRFV P)) ↔
    ∃ e, τ e ≤ g ∧ u.Precedes (τ e) ∧ P w e := by
  rw [future, MOD_eq, present_eq_of_isLowerSet fun _ ↦ isLowerSet_prospective _ _]
  exact mem_prospective_Iic_prfv

-- (68) under the rule (28)
theorem mem_present_compl_future_iff :
    w ∈ present u (fun v ↦ (future s R g (PRFV P) v)ᶜ) ↔
      ∀ e, τ e ≤ g → P w e → (τ e).fst ≤ u.fst := by
  rw [future, MOD_eq]
  refine ⟨fun h e hg hP ↦ not_lt.1 fun hlt ↦ ?_, fun h t ht hmem ↦ ?_⟩
  · exact h (show .pure u.fst ≤ u from NonemptyInterval.le_def.2 ⟨le_rfl, u.fst_le_snd⟩)
      (mem_prospective_Iic_prfv.2 ⟨e, hg, hlt, hP⟩)
  · obtain ⟨e, hg, hlt, hP⟩ := mem_prospective_Iic_prfv.1 hmem
    exact ((h e hg hP).trans ((NonemptyInterval.le_def.1 ht).1.trans t.fst_le_snd)).not_gt hlt

-- (77): without the prospective the modal leaves the negated stative its present reading
theorem present_compl_MOD_prfv :
    present u (fun v ↦ (MOD s R (PRFV P) v)ᶜ) = {w | u ∉ PRFV P w} := by
  rw [MOD_eq, present_eq_of_isLowerSet fun w ↦ isLowerSet_compl_prfv P w]
  rfl

/-- With one subject's eventualities within the utterance time and the other's after it (26a),
the non-past sentence is true, and the sentence is false on the present structure and on the
future structure alike. -/
theorem nonPast_and_not_present_of_split (hP : ∃ e, P w e) (hQ : ∃ e, Q w e)
    (hP' : ∀ e, P w e → τ e ≤ u) (hQ' : ∀ e, Q w e → u.Precedes (τ e)) :
    w ∈ nonPast u (fun v ↦ PRFV P v ∩ PRFV Q v) ∧
      w ∉ present u (fun v ↦ PRFV P v ∩ PRFV Q v) ∧
      w ∉ present u (future s R g fun v ↦ PRFV P v ∩ PRFV Q v) := by
  obtain ⟨e₁, h₁⟩ := hP
  obtain ⟨e₂, h₂⟩ := hQ
  refine ⟨?_, fun h ↦ not_mem_prfv_of_forall_precedes hQ' (present_subset h).2, fun h ↦ ?_⟩
  · rw [nonPast_prfv_inter, nonPast_prfv, nonPast_prfv]
    exact ⟨⟨e₁, (NonemptyInterval.le_def.1 (hP' e₁ h₁)).1, h₁⟩,
      e₂, u.fst_le_snd.trans (hQ' e₂ h₂).le, h₂⟩
  · rw [future, MOD_eq] at h
    obtain ⟨j, ⟨-, ⟨e, hle, he⟩, -⟩, hj⟩ := present_subset h
    exact (((NonemptyInterval.le_def.1 hle).1.trans
      ((τ e).fst_le_snd.trans (NonemptyInterval.le_def.1 (hP' e he)).2)).not_gt hj)

omit [∀ t, (R t).IsRefl] in
-- negation beneath the prospective is consistent with the affirmative future
theorem exists_prospective_compl_prfv :
    ∃ (P : Unit → NonemptyInterval ℤ → Prop) (u g : NonemptyInterval ℤ),
      u ∈ prospective (fun v ↦ Iic g ∩ PRFV P v) () ∧
        u ∈ prospective (fun v ↦ Iic g ∩ (PRFV P v)ᶜ) () := by
  refine ⟨fun _ e ↦ e = .pure 1, .pure 0, ⟨(1, 2), by decide⟩,
    mem_prospective_Iic_prfv.2 ⟨.pure 1, by decide, by decide, rfl⟩,
    .pure 2, ⟨by decide, ?_⟩, by decide⟩
  rintro ⟨e, hle, rfl⟩
  exact absurd hle (by decide)

/-! ### The readings of a bare verb -/

/-- A predicate is of an Aktionsart when it is stative and has the subinterval property, or
eventive and its events take time. -/
def Describes : Dynamicity → (Unit → NonemptyInterval ℤ → Prop) → Prop
  | .stative, P => HasSubintervalProperty P
  | .dynamic, P => ∀ w e, P w e → (τ e).fst < (τ e).snd

/-- A bare verb of an Aktionsart has a present reading when some predicate of the Aktionsart
verifies the present perfective, and a future reading when one verifies the prospective, the
modal being the identity over a realistic base. -/
def Available (c : Dynamicity) : Tense → Prop
  | .present => ∃ P u, Describes c P ∧ () ∈ present u (PRFV P)
  | .future => ∃ P u g, Describes c P ∧ u ∈ prospective (fun v ↦ Iic g ∩ PRFV P v) ()
  | .past => False

-- the predicate true of every interval is stative
private theorem describes_stative_true : Describes .stative fun _ _ ↦ True :=
  hasSubintervalProperty_iff_witnesses.2 fun _ _ _ t _ ↦ ⟨t, rfl, trivial⟩

theorem available_iff {c : Dynamicity} {t : Tense} :
    Available c t ↔ t = .future ∨ t = .present ∧ c = .stative := by
  cases t
  · simp [Available]
  · cases c
    · simp only [Available, Describes, reduceCtorEq, and_false, or_false, iff_false, not_exists,
        not_and]
      exact fun P u h ↦ not_mem_present_prfv_of_forall_lt (h ())
    · exact iff_of_true ⟨fun _ _ ↦ True, .pure 0, describes_stative_true,
        mem_present_prfv.2 fun a _ ↦ ⟨.pure a, rfl, trivial⟩⟩ (.inr ⟨rfl, rfl⟩)
  · refine iff_of_true ?_ (.inl rfl)
    cases c
    · exact ⟨fun _ e ↦ e = ⟨(1, 2), by decide⟩, .pure 0, ⟨(1, 2), by decide⟩,
        fun _ e he ↦ by subst he; decide,
        mem_prospective_Iic_prfv.2 ⟨_, le_rfl, by decide, rfl⟩⟩
    · exact ⟨fun _ _ ↦ True, .pure 0, .pure 1, describes_stative_true,
        mem_prospective_Iic_prfv.2 ⟨.pure 1, le_rfl, by decide, trivial⟩⟩

instance (c : Dynamicity) (t : Tense) : Decidable (Available c t) :=
  decidable_of_iff _ available_iff.symm

/-- A row's Aktionsart and the temporal reference its adverbial fixes. -/
def reading (e : Datum) : Option (Dynamicity × Tense) := do
  let c ← e.parse? "aktionsart" [("eventive", .dynamic), ("stative", .stative)]
  let t ← e.parse? "adverbial" [("now", .present), ("tomorrow", .future)]
  pure (c, t)

/-- The Aktionsart of a bare verb in *-nA* predicts its readings: the eventives of (7) are out
with *odoo* 'now' and fine with *margaash* 'tomorrow', and the statives of (8) are fine with
both. -/
theorem available_rows :
    Datum.Checks reading (fun r ↦ .ofProp (Available r.1 r.2)) Examples.all 8 := by
  decide

end Knick2026
