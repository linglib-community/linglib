module

public import Linglib.Data.Examples.Knick2026
public import Linglib.Data.Examples.Readers
public import Linglib.Semantics.Aspect.SubintervalProperty
public import Linglib.Semantics.Conditionals.SelectionFunction

/-!
# Knick (2026): Future shifting with present marking in Khalkha Mongolian

Knick argues that Khalkha *-nA*, described as a non-past, is a present tense. A non-past sentence
with conjoined subjects would be [true when each conjunct holds at its own
time](##nonPast_prfv_inter), and a non-past perfect [true of an event at any
time](##nonPast_perfect_prfv). The bare verb is perfective, and a simple present must hold at
every part of the utterance time, so it holds only where [every moment is the run time of an
eventuality](##mem_simplePresent), as with a state. The future has a silent selectional modal over
a silent prospective: at a world of its base it says that [an eventuality
follows](##mem_future_iff), and it [commutes with negation](##compl_future). The Aktionsart of a
bare verb thus [predicts its readings](##available_rows).

## Implementation notes

* A sentence is the set of worlds in which it holds at the utterance time, an interval; the
  present tense is evaluation there, and the non-past quantifies over reference times no part of
  which precedes it.
* The perfect is the library's, whose span ends with the reference interval, where the paper's
  may end before it; the non-past perfect is the same on either.
* A subject's eventualities are those of its predicate, and a distributive reading of conjoined
  subjects places an eventuality of each within the reference time.
* The modal base at the utterance time is a relation between worlds, the base of a world its
  successors. A circumstantial base is realistic, which the theorems state as the world of
  evaluation being its own successor.
* Negation is interpreted where the paper's structure for the negated future has it, above the
  modal and the prospective. Beneath the prospective it would negate the perfective at some
  future time within the salient interval, which
  [the affirmative leaves open](##exists_prospective_compl_prfv).
* A stative predicate is one with the subinterval property and an eventive predicate one whose
  events take time; achievements, which are instantaneous, fail the present perfective
  [by not recurring at every moment](##not_mem_simplePresent_of_subsingleton).

## TODO

* The restriction of the prospective to the perfective is the paper's stipulation and is built
  into the future structure; the present-only readings of the perfect and the imperfective are
  not derived.
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

open Aspect Conditional Set
open Event (τ)
open scoped SetRel

variable {W T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] {P Q : W → E → Prop}
  {p : W → Set (NonemptyInterval T)} {u g : NonemptyInterval T} {w : W}

/-! ### The non-past -/

/-- (20): the non-past holds where the property holds of a reference time no part of which
precedes the utterance time `u`. -/
def nonPast (u : NonemptyInterval T) (p : W → Set (NonemptyInterval T)) : Set W :=
  {w | ∃ t ∈ p w, ∀ j ≤ t, ¬ j.Precedes u}

theorem mem_nonPast : w ∈ nonPast u p ↔ ∃ t ∈ p w, u.fst ≤ t.fst := by
  refine exists_congr fun t ↦ and_congr_right fun _ ↦ ⟨fun h ↦ ?_, fun h j hj hlt ↦ ?_⟩
  · exact not_lt.1 (h (.pure t.fst) (NonemptyInterval.le_def.2 ⟨le_rfl, t.fst_le_snd⟩))
  · exact (h.trans ((NonemptyInterval.le_def.1 hj).1.trans j.fst_le_snd)).not_gt hlt

theorem nonPast_prfv : nonPast u (PRFV P) = {w | ∃ e, u.fst ≤ (τ e).fst ∧ P w e} := by
  ext w
  rw [mem_nonPast]
  exact ⟨fun ⟨_, ⟨e, hle, hP⟩, h⟩ ↦ ⟨e, h.trans (NonemptyInterval.le_def.1 hle).1, hP⟩,
    fun ⟨e, h, hP⟩ ↦ ⟨τ e, ⟨e, le_rfl, hP⟩, h⟩⟩

/-- A non-past sentence with conjoined subjects, each with an eventuality within the reference
time, is true whenever each conjunct is true by itself, as when one subject knows Icelandic now
and the other will later (26a); the sentence is not so used. -/
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

-- (26a): the present is false when one subject's eventualities all lie ahead
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
theorem not_mem_perfect_prfv_of_forall_precedes (h : ∀ e, P w e → u.Precedes (τ e)) :
    u ∉ perfect (PRFV P) w := fun hu ↦
  let ⟨e, hle, hP⟩ := mem_perfect_prfv.1 hu
  (((τ e).fst_le_snd.trans hle).not_gt (h e hP))

/-! ### The present perfective -/

/-- (35b) under the rule (28): the simple present of a bare verb, the present over the perfective,
holds where the perfective holds at every part of the utterance time `u`. -/
def simplePresent (P : W → E → Prop) (u : NonemptyInterval T) : Set W :=
  {w | u ∈ durative (PRFV P) w}

-- every moment of the utterance time is the run time of an eventuality
theorem mem_simplePresent : w ∈ simplePresent P u ↔ ∀ a ∈ u, ∃ e, τ e = .pure a ∧ P w e :=
  mem_durative_prfv

-- at an instant an instantaneous eventuality suffices, as for [bennett-partee-1972]
theorem mem_simplePresent_pure {a : T} :
    w ∈ simplePresent P (.pure a) ↔ ∃ e, τ e = .pure a ∧ P w e := by
  simp [mem_simplePresent, NonemptyInterval.mem_pure]

-- (41b)
theorem not_mem_simplePresent_of_forall_lt (h : ∀ e, P w e → (τ e).fst < (τ e).snd) :
    w ∉ simplePresent P u := fun hw ↦
  let ⟨e, he, hP⟩ := mem_simplePresent.1 hw u.fst ⟨le_rfl, u.fst_le_snd⟩
  lt_irrefl u.fst (by simpa [he] using h e hP)

-- (46a)
theorem not_mem_simplePresent_of_subsingleton (hu : u.fst < u.snd)
    (h : ∀ e e', P w e → P w e' → τ e = τ e') : w ∉ simplePresent P u := fun hw ↦ by
  obtain ⟨e, he, hP⟩ := mem_simplePresent.1 hw u.fst ⟨le_rfl, u.fst_le_snd⟩
  obtain ⟨e', he', hP'⟩ := mem_simplePresent.1 hw u.snd ⟨u.fst_le_snd, le_rfl⟩
  exact hu.ne (by simpa [he, he'] using congrArg (·.fst) (h e e' hP hP'))

-- (48b), (51)
theorem mem_simplePresent_of_unbounded (h : HasSubintervalProperty P) (hu : u ∈ UNBOUNDED P w) :
    w ∈ simplePresent P u :=
  h.unbounded_subset_durative_prfv w hu

/-! ### The future -/

/-- (38) over the perfective: the prospective holds where the utterance time `u` precedes a time
within the salient interval `g` that contains an eventuality of the predicate. -/
def prospectivePerfective (g : NonemptyInterval T) (P : W → E → Prop) (u : NonemptyInterval T) :
    Set W :=
  {w | u ∈ prospective (fun v ↦ Iic g ∩ PRFV P v) w}

theorem mem_prospectivePerfective :
    w ∈ prospectivePerfective g P u ↔ ∃ e, τ e ≤ g ∧ u.Precedes (τ e) ∧ P w e :=
  ⟨fun ⟨_, ⟨hg, e, hle, hP⟩, hj⟩ ↦
      ⟨e, hle.trans hg, hj.trans_le (NonemptyInterval.le_def.1 hle).1, hP⟩,
    fun ⟨e, hg, hlt, hP⟩ ↦ ⟨τ e, ⟨hg, e, le_rfl, hP⟩, hlt⟩⟩

-- the rule (28) does not exclude the future structure
theorem prospectivePerfective_anti {u' : NonemptyInterval T} (h : u' ≤ u) :
    prospectivePerfective g P u ⊆ prospectivePerfective g P u' :=
  fun _ hw ↦ isLowerSet_prospective _ _ h hw

variable (s : SelectionFunction W) (R : SetRel W W)

/-- (35a) with the modal of (71): the future structure, the present over the modal over the
prospective over the perfective, holds where the prospective holds at the world selected from
the modal base `R`. -/
def future (g : NonemptyInterval T) (P : W → E → Prop) (u : NonemptyInterval T) : Set W :=
  s.modal R (prospectivePerfective g P u)

variable {s R}

/-- At a world of its own modal base the future holds where an eventuality of the predicate lies
within the salient interval after the utterance time (42): selection returns the world of
evaluation, and the modal adds nothing to the truth conditions. -/
theorem mem_future_iff (h : w ~[R] w) :
    w ∈ future s R g P u ↔ ∃ e, τ e ≤ g ∧ u.Precedes (τ e) ∧ P w e := by
  rw [future, SelectionFunction.mem_modal, SelectionFunction.along_eq_self h,
    mem_prospectivePerfective]

/-- Negation above the modal is negation beneath it (72): the negated future (68), with *-kh*
for the modal, holds where no eventuality follows at the selected world. -/
theorem compl_future : (future s R g P u)ᶜ = s.modal R (prospectivePerfective g P u)ᶜ :=
  (map_compl' _ _).symm

theorem mem_compl_future_iff (h : w ~[R] w) :
    w ∈ (future s R g P u)ᶜ ↔ ∀ e, τ e ≤ g → u.Precedes (τ e) → ¬ P w e := by
  simp [mem_future_iff h]

-- (77): without the prospective the modal leaves the negated stative its present reading
theorem mem_modal_compl_prfv (h : w ~[R] w) : w ∈ s.modal R {v | u ∉ PRFV P v} ↔ u ∉ PRFV P w := by
  rw [SelectionFunction.mem_modal, SelectionFunction.along_eq_self h, mem_ofPred_eq]

-- negation beneath the prospective is consistent with the affirmative future
theorem exists_prospective_compl_prfv :
    ∃ (P : Unit → NonemptyInterval ℤ → Prop) (u g : NonemptyInterval ℤ),
      () ∈ prospectivePerfective g P u ∧ u ∈ prospective (fun v ↦ Iic g ∩ (PRFV P v)ᶜ) () := by
  refine ⟨fun _ e ↦ e = .pure 1, .pure 0, ⟨(1, 2), by decide⟩,
    mem_prospectivePerfective.2 ⟨.pure 1, by decide, by decide, rfl⟩,
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
modal being idle at a world of its base. -/
def Available (c : Dynamicity) : Tense → Prop
  | .present => ∃ P u, Describes c P ∧ () ∈ simplePresent P u
  | .future => ∃ P u g, Describes c P ∧ () ∈ prospectivePerfective g P u
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
      exact fun P u h ↦ not_mem_simplePresent_of_forall_lt (h ())
    · exact iff_of_true ⟨fun _ _ ↦ True, .pure 0, describes_stative_true,
        mem_simplePresent.2 fun a _ ↦ ⟨.pure a, rfl, trivial⟩⟩ (.inr ⟨rfl, rfl⟩)
  · refine iff_of_true ?_ (.inl rfl)
    cases c
    · exact ⟨fun _ e ↦ e = ⟨(1, 2), by decide⟩, .pure 0, ⟨(1, 2), by decide⟩,
        fun _ e he ↦ by subst he; decide,
        mem_prospectivePerfective.2 ⟨_, le_rfl, by decide, rfl⟩⟩
    · exact ⟨fun _ _ ↦ True, .pure 0, .pure 1, describes_stative_true,
        mem_prospectivePerfective.2 ⟨.pure 1, le_rfl, by decide, trivial⟩⟩

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
