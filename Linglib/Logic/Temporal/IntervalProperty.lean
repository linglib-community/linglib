module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Logic.Modal.Basic
public import Mathlib.Order.Hom.BoundedLattice

/-!
# Interval properties

An interval property is a predicate of intervals of time, `NonemptyInterval T → Prop`, ordered
pointwise: the property of the intervals at which a clause holds, of the run times of the events
of a kind, or of the spans an adverbial names. The property `(· = i)` holds of the one interval
`i`, and `(· ≤ i)` of `i` and its subintervals, as a state that lasts throughout `i` does.

Operators on interval properties are possibility and necessity, `◇[R]` and `□[R]`, along
relations between intervals. Along inclusion, `{x | x.2 ≤ x.1}`, `inclusive p` holds at `t` when
`p` holds at some
subinterval of `t`, and `durative p` when `p` holds at every subinterval of `t`. A monotone
interval property is one closed under superintervals, and an antitone one is closed under
subintervals: `inclusive p` is monotone and equals `p` when `p` is monotone, and `durative p` is
antitone and equals `p` when `p` is antitone. Possibility over superintervals,
`◇[{x | x.1 ≤ x.2}] p`, is left adjoint to `durative`, and what it yields is antitone.

The time trace `timeTrace p` of an interval property is the set of moments its intervals cover,
which are the moments `a` at which `p` is possible along containment,
`◇[{x | x.1 ≤ x.2}] p (.pure a)`. The trace of `(· = i)` and of `(· ≤ i)` is `i`.

## Main definitions

* `Temporal.inclusive`, `Temporal.durative`: possibility and necessity over subintervals.
* `Temporal.timeTrace`: the moments an interval property covers.
* `Temporal.timeTraceSupBotHom`: the time trace as a map preserving joins and the bottom.

## Implementation notes

* An interval property is a predicate, as the propositions of `Logic/Modal` are, so that `◇[R]`
  and `□[R]` apply to it and entailment is `≤`. Its time trace is a set of moments, to which the
  bounds and closures of a set in an order apply.
* The file makes no assumption about what an interval property is the property of, and needs
  only the order of intervals. Viewpoint aspect (`Semantics/Aspect`) applies operators along the
  elements of the interval algebra to the run times of events, and a temporal connective
  (`Semantics/Tense`) relates the time traces of its two clauses.

## References

* [dowty-1979]
* [krifka-1989]
-/

@[expose] public section

namespace Temporal

open ModalLogic
open scoped SetRel

variable {T : Type*} [Preorder T] {p q : NonemptyInterval T → Prop} {s t : NonemptyInterval T}

/-! ### Subintervals and superintervals -/

/-- `inclusive p` holds at an interval when `p` holds at some subinterval of it, the inclusive
reading of an interval adverbial, *in*. -/
def inclusive (p : NonemptyInterval T → Prop) : NonemptyInterval T → Prop :=
  ◇[{x : NonemptyInterval T × NonemptyInterval T | x.2 ≤ x.1}] p

/-- `durative p` holds at an interval when `p` holds at every subinterval of it, the durative
reading of an interval adverbial, *throughout*. -/
def durative (p : NonemptyInterval T → Prop) : NonemptyInterval T → Prop :=
  □[{x : NonemptyInterval T × NonemptyInterval T | x.2 ≤ x.1}] p

theorem inclusive_iff : inclusive p t ↔ ∃ s ≤ t, p s := by
  simp [inclusive, diamond_iff]

theorem durative_iff : durative p t ↔ ∀ s ≤ t, p s := by
  simp [durative, box_iff]

theorem inclusive_mono : Monotone (inclusive : (NonemptyInterval T → Prop) → _) := diamond_mono _

theorem durative_mono : Monotone (durative : (NonemptyInterval T → Prop) → _) := box_mono _

theorem le_inclusive (p : NonemptyInterval T → Prop) : p ≤ inclusive p :=
  fun t h ↦ inclusive_iff.2 ⟨t, le_rfl, h⟩

theorem durative_le (p : NonemptyInterval T → Prop) : durative p ≤ p :=
  fun t h ↦ durative_iff.1 h t le_rfl

theorem durative_le_inclusive (p : NonemptyInterval T → Prop) : durative p ≤ inclusive p :=
  (durative_le p).trans (le_inclusive p)

/-- An inclusive property is closed under superintervals. -/
theorem monotone_inclusive (p : NonemptyInterval T → Prop) : Monotone (inclusive p) :=
  fun _ _ hle h ↦ let ⟨s, hs, hp⟩ := inclusive_iff.1 h; inclusive_iff.2 ⟨s, hs.trans hle, hp⟩

/-- A durative property is closed under subintervals. -/
theorem antitone_durative (p : NonemptyInterval T → Prop) : Antitone (durative p) :=
  fun _ _ hle h ↦ durative_iff.2 fun s hs ↦ durative_iff.1 h s (hs.trans hle)

/-- A property closed under superintervals is its own inclusive reading. -/
theorem inclusive_eq_of_monotone (hp : Monotone p) : inclusive p = p :=
  le_antisymm (fun _ h ↦ let ⟨_, hs, hps⟩ := inclusive_iff.1 h; hp hs hps) (le_inclusive p)

/-- A property closed under subintervals is its own durative reading. -/
theorem durative_eq_of_antitone (hp : Antitone p) : durative p = p :=
  le_antisymm (durative_le p) fun _ h ↦ durative_iff.2 fun _ hs ↦ hp hs h

@[simp] theorem inclusive_inclusive (p : NonemptyInterval T → Prop) :
    inclusive (inclusive p) = inclusive p :=
  inclusive_eq_of_monotone (monotone_inclusive p)

@[simp] theorem durative_durative (p : NonemptyInterval T → Prop) :
    durative (durative p) = durative p :=
  durative_eq_of_antitone (antitone_durative p)

/-- A property closed under superintervals holds throughout an interval exactly when it holds at
every moment of the interval. -/
theorem durative_iff_of_monotone (hp : Monotone p) : durative p t ↔ ∀ a ∈ t, p (.pure a) := by
  rw [durative_iff]
  refine ⟨fun h a ha ↦ h _ (NonemptyInterval.pure_le_iff.2 ha), fun h s hs ↦ ?_⟩
  obtain ⟨h₁, h₂⟩ := NonemptyInterval.le_def.1 hs
  exact hp (NonemptyInterval.pure_le_iff.2 ⟨le_rfl, s.fst_le_snd⟩)
    (h s.fst ⟨h₁, s.fst_le_snd.trans h₂⟩)

/-! ### Superintervals

Possibility along containment, `◇[{x | x.1 ≤ x.2}] p`, holds at an interval when `p` holds at
some interval that contains it. -/

/-- Possibility over superintervals is left adjoint to necessity over subintervals. -/
theorem gc_diamond_le_durative :
    GaloisConnection
      (fun p : NonemptyInterval T → Prop ↦
        ◇[{x : NonemptyInterval T × NonemptyInterval T | x.1 ≤ x.2}] p)
      durative :=
  diamond_box_gc _

/-- A property that holds at some superinterval is closed under subintervals. -/
theorem antitone_diamond_le (p : NonemptyInterval T → Prop) :
    Antitone (◇[{x : NonemptyInterval T × NonemptyInterval T | x.1 ≤ x.2}] p) :=
  fun _ _ hst ⟨u, hu, hp⟩ ↦ ⟨u, le_trans hst hu, hp⟩

theorem durative_diamond_le (p : NonemptyInterval T → Prop) :
    durative (◇[{x : NonemptyInterval T × NonemptyInterval T | x.1 ≤ x.2}] p) =
      ◇[{x : NonemptyInterval T × NonemptyInterval T | x.1 ≤ x.2}] p :=
  durative_eq_of_antitone (antitone_diamond_le p)

/-! ### The time trace -/

end Temporal

namespace Temporal

section Preorder

variable {T : Type*} [Preorder T] {p q : NonemptyInterval T → Prop} {a : T}
  {i : NonemptyInterval T}

/-- The time trace of an interval property is the set of moments that its intervals contain. -/
def timeTrace (p : NonemptyInterval T → Prop) : Set T := {a | ∃ i, p i ∧ a ∈ i}

@[simp] theorem mem_timeTrace : a ∈ timeTrace p ↔ ∃ i, p i ∧ a ∈ i := .rfl

/-- The time trace of the intervals `f x` for `x` in a set. -/
theorem timeTrace_exists_mem {α : Type*} (f : α → NonemptyInterval T) (s : Set α) :
    timeTrace (fun i ↦ ∃ x ∈ s, f x = i) = {a | ∃ x ∈ s, a ∈ f x} := by
  ext; simp

theorem timeTrace_mono : Monotone (timeTrace : (NonemptyInterval T → Prop) → Set T) :=
  fun _ _ h _ ⟨i, hi, ha⟩ ↦ ⟨i, h i hi, ha⟩

@[simp] theorem timeTrace_bot : timeTrace (⊥ : NonemptyInterval T → Prop) = ∅ := by
  ext; simp

@[simp] theorem timeTrace_top : timeTrace (⊤ : NonemptyInterval T → Prop) = Set.univ :=
  Set.eq_univ_of_forall fun a ↦ ⟨.pure a, trivial, le_rfl, le_rfl⟩

@[simp] theorem timeTrace_sup (p q : NonemptyInterval T → Prop) :
    timeTrace (p ⊔ q) = timeTrace p ∪ timeTrace q := by
  ext; simp [or_and_right, exists_or]

/-- The time trace as a map preserving joins and the bottom. -/
def timeTraceSupBotHom : SupBotHom (NonemptyInterval T → Prop) (Set T) where
  toFun := timeTrace
  map_sup' := timeTrace_sup
  map_bot' := timeTrace_bot

@[simp] theorem coe_timeTraceSupBotHom :
    ⇑(timeTraceSupBotHom (T := T)) = timeTrace := rfl

theorem isLeast_timeTrace_eq (i : NonemptyInterval T) : IsLeast (timeTrace (· = i)) i.fst :=
  ⟨⟨i, rfl, le_rfl, i.fst_le_snd⟩, fun _ ⟨_, hj, ha⟩ ↦ (hj ▸ ha).1⟩

theorem isGreatest_timeTrace_eq (i : NonemptyInterval T) :
    IsGreatest (timeTrace (· = i)) i.snd :=
  ⟨⟨i, rfl, i.fst_le_snd, le_rfl⟩, fun _ ⟨_, hj, ha⟩ ↦ (hj ▸ ha).2⟩

end Preorder

section PartialOrder

variable {T : Type*} [PartialOrder T] {a : T} {i : NonemptyInterval T}

@[simp] theorem timeTrace_eq (i : NonemptyInterval T) : timeTrace (· = i) = (i : Set T) := by
  ext; simp

theorem mem_timeTrace_eq_pure {b : T} : a ∈ timeTrace (· = NonemptyInterval.pure b) ↔ a = b := by
  simp

@[simp] theorem timeTrace_subintervals (i : NonemptyInterval T) :
    timeTrace (· ≤ i) = (i : Set T) :=
  Set.ext fun _ ↦ ⟨fun ⟨_, hj, ha⟩ ↦ NonemptyInterval.coe_subset_coe.2 hj ha,
    fun ha ↦ ⟨i, le_rfl, ha⟩⟩

theorem mem_timeTrace_subintervals : a ∈ timeTrace (· ≤ i) ↔ a ∈ i := by
  rw [timeTrace_subintervals]; rfl

theorem isLeast_timeTrace_subintervals (i : NonemptyInterval T) :
    IsLeast (timeTrace (· ≤ i)) i.fst := by
  rw [timeTrace_subintervals, ← timeTrace_eq]
  exact isLeast_timeTrace_eq i

theorem isGreatest_timeTrace_subintervals (i : NonemptyInterval T) :
    IsGreatest (timeTrace (· ≤ i)) i.snd := by
  rw [timeTrace_subintervals, ← timeTrace_eq]
  exact isGreatest_timeTrace_eq i

end PartialOrder

open ModalLogic in
/-- The time trace holds the moments at which the property is possible along containment. -/
theorem mem_timeTrace_iff_diamond {T : Type*} [PartialOrder T] {p : NonemptyInterval T → Prop}
    {a : T} :
    a ∈ timeTrace p ↔ ◇[{x : NonemptyInterval T × NonemptyInterval T | x.1 ≤ x.2}] p (.pure a) := by
  simp only [mem_timeTrace, diamond_iff]
  exact exists_congr fun i ↦ and_comm.trans (and_congr_left fun _ ↦
    NonemptyInterval.pure_le_iff.symm)

end Temporal
