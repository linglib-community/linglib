module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Semantics.Tense.Defs
public import Linglib.Data.Examples.Eckardt2006

/-!
# Eckardt (2006): Meaning Change in Grammaticalization

In *semantic reanalysis* a sentence keeps the information it conveys while that information is
composed in a new way, and what was an inference from the literal content becomes the literal
content. This file follows the emergence of the English *going to* future.

Movement *go* with an infinitive denotes the goings of `x` that prepare an event of the embedded
predicate: `goTo go prepare P x w e` holds when `go x w e` and `prepare e e'` and `P x w e'` for
some `e'`. Like any event predicate it takes a viewpoint, and in the progressive the reference
time lies within the going. The reanalysed *be going to* is an interval property: `beGoingTo imm P
x w` holds of a reference time `t` when `t` precedes an event `e` of `P x w` with `imm t e`, where
`imm` says which events count as imminent at a time.

When a preparation precedes what it prepares, and a going in progress makes what it prepares
imminent, the progressive of the old entry is included in the new one
(`unbounded_goTo_subset_beGoingTo`): the inference that the planned event is imminent is a
consequence of where the reference time lies. The inclusion holds under the present and under
every tense (`atPoint_goTo_subset`, `diamond_goTo_le`), and in each world of the modal domain of
the imperfective (`impf_goTo_subset`). The new entry is a restriction of the prospective viewpoint
(`beGoingTo_subset_prosp`) and conveys no movement (`unbounded_goTo_eq_empty`).

The old entry holds of nothing when no going prepares an event of the embedded predicate, under
every viewpoint (`ofRel_goTo_eq_empty`). A simple form has only the old entry, so it is acceptable
only where the embedded clause allows the movement interpretation, and German *gehen*, which has
no future entry, behaves in every form as the English simple forms do (`licensed_iff`).

## Implementation notes

* The progressive is the extensional `UNBOUNDED`, the reference time within the run time of the
  event, as in the source. `impf_goTo_subset` states the inclusion for the modal imperfective,
  where an event in progress need not be completed: there the planned event follows the reference
  time in every world of the modal domain, and in the world of evaluation only if it belongs to
  that domain.
* The new entry has strict precedence, the reference time ending before the event starts, where
  `PROSP` allows the two to meet.
* `goTo` is an event predicate and `beGoingTo` an interval property. That the progressive is no
  longer a part of the reanalysed sentence is this difference of type: no viewpoint operator
  applies to the new entry.
* `imm` is the one parameter of the new entry that the context supplies and the old entry lacks.

## TODO

* The manner adverbs that the new entry excludes, *carefully going to travel*, are not treated.
* The other reanalyses of the book (the French negation particles, *selbst*, *lauter*) would decide
  whether semantic reanalysis is to be a definition and not a pair of theorems for each case.

## References

* [eckardt-2006]
-/

@[expose] public section

namespace Eckardt2006

open Aspect ModalLogic PointAlgebra
open scoped Denotes SetRel
open Event (τ)
open Examples (Example Verb Form Movement)

variable {W X E T : Type*} [LinearOrder T] [TemporalTrace E T]
  {go : X → W → E → Prop} {prepare : E → E → Prop} {P : X → W → E → Prop}
  {imm imm' : NonemptyInterval T → E → Prop} {x : X} {w : W} {t : NonemptyInterval T}

/-! ### The two entries -/

/-- (4.50a): Movement *go* with an infinitive holds of a going by `x` that prepares an event in
which `x` does what the embedded clause describes. -/
def goTo (go : X → W → E → Prop) (prepare : E → E → Prop) (P : X → W → E → Prop) (x : X) :
    W → E → Prop :=
  fun w e ↦ go x w e ∧ ∃ e', prepare e e' ∧ P x w e'

/-- (4.58): The reanalysed *be going to* holds of a reference time that precedes an imminent event
of the embedded predicate. -/
def beGoingTo (imm : NonemptyInterval T → E → Prop) (P : X → W → E → Prop) (x : X) :
    W → Set (NonemptyInterval T) :=
  fun w ↦ {t | ∃ e, t.Precedes (τ e) ∧ imm t e ∧ P x w e}

@[simp] theorem mem_beGoingTo :
    t ∈ beGoingTo imm P x w ↔ ∃ e, t.Precedes (τ e) ∧ imm t e ∧ P x w e := Iff.rfl

theorem beGoingTo_mono (h : ∀ t e, imm t e → imm' t e) :
    beGoingTo imm P x w ⊆ beGoingTo imm' P x w :=
  fun _ ⟨e, ht, hi, hP⟩ ↦ ⟨e, ht, h _ _ hi, hP⟩

/-- The reanalysed *be going to* is a restriction of the prospective viewpoint. -/
theorem beGoingTo_subset_prosp : beGoingTo imm P x w ⊆ PROSP (P x) w :=
  fun _ ⟨e, ht, _, hP⟩ ↦ ⟨e, le_of_lt ht, hP⟩

/-! ### From the inference to the literal content -/

section Inference

variable (hprep : ∀ e e', prepare e e' → Event.Precedes e e')
  (himm : ∀ w t e e', go x w e → prepare e e' → t ≤ τ e → imm t e')

include hprep himm

/-- (4.54): Where preparations precede what they prepare and a going in progress makes what it
prepares imminent, the progressive of movement *go* is included in the reanalysed *be going
to*. -/
theorem unbounded_goTo_subset_beGoingTo :
    UNBOUNDED (goTo go prepare P x) w ⊆ beGoingTo imm P x w := by
  rintro t ⟨e, hte, hgo, e', hpr, hP⟩
  exact ⟨e', lt_of_le_of_lt (NonemptyInterval.le_def.1 hte).2 (hprep e e' hpr),
    himm w t e e' hgo hpr hte, hP⟩

-- (4.50f) and (4.56): the inclusion under the present tense.
theorem atPoint_goTo_subset :
    atPoint (UNBOUNDED (goTo go prepare P x)) ⊆ atPoint (beGoingTo imm P x) :=
  fun _ hs ↦ unbounded_goTo_subset_beGoingTo hprep himm hs

-- (4.51) and (4.60): the inclusion under every tense.
theorem diamond_goTo_le (tn : Tense) :
    ◇[toSetRel ⟦tn⟧] (fun r ↦ (⟨w, r⟩ : Index W T) ∈ atPoint (UNBOUNDED (goTo go prepare P x))) ≤
      ◇[toSetRel ⟦tn⟧] (fun r ↦ (⟨w, r⟩ : Index W T) ∈ atPoint (beGoingTo imm P x)) :=
  diamond_mono _ fun _ hr ↦ atPoint_goTo_subset hprep himm hr

-- The inclusion in each world of the modal domain of the imperfective.
theorem impf_goTo_subset {acc : W → NonemptyInterval T → Set W} :
    IMPF acc (goTo go prepare P x) w ⊆ {t | ∀ v ∈ acc w t, t ∈ beGoingTo imm P x v} :=
  fun _ ht v hv ↦ unbounded_goTo_subset_beGoingTo hprep himm (ht v hv)

end Inference

-- The reference time of a progressive is not before its own event.
theorem not_precedes_of_le {s : NonemptyInterval T} (h : t ≤ s) : ¬ t.Precedes s :=
  fun hp ↦ absurd (lt_of_le_of_lt ((NonemptyInterval.le_def.1 h).1.trans t.fst_le_snd) hp)
    (lt_irrefl _)

/-! ### What the new entry no longer conveys -/

/-- Movement *go* with an infinitive holds at no reference time, under any viewpoint, when no
going prepares an event of the embedded predicate. -/
theorem ofRel_goTo_eq_empty (R : NonemptyInterval T → NonemptyInterval T → Prop)
    (h : ∀ e e', go x w e → prepare e e' → ¬ P x w e') : ofRel R (goTo go prepare P x) w = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ⟨e, _, hgo, e', hpr, hP⟩ ↦ h e e' hgo hpr hP

theorem unbounded_goTo_eq_empty (h : ∀ e, ¬ go x w e) :
    UNBOUNDED (goTo go prepare P x) w = ∅ :=
  ofRel_goTo_eq_empty _ fun e _ hgo _ ↦ (h e hgo).elim

-- A time at which something is going to happen though nothing moves.
theorem pure_mem_beGoingTo :
    (.pure 0 : NonemptyInterval ℕ) ∈
      beGoingTo (E := NonemptyInterval ℕ) (fun _ _ ↦ True)
        (fun (_ _ : Unit) e ↦ e = .pure 1) () () :=
  ⟨.pure 1, Nat.zero_lt_one, trivial, rfl⟩

/-! ### Simple forms and German *gehen* -/

/-- The two entries of a verb of movement with an infinitive. -/
inductive Entry where
  /-- The going prepares what the embedded clause describes. -/
  | movement
  /-- What the embedded clause describes is imminent. -/
  | future
  deriving DecidableEq, Fintype, Repr

/-- The entries a form of a verb has: every form has the movement entry, and only *be going to*
the future one. -/
def Entry.Available : Entry → Verb → Form → Prop
  | .movement, _, _ => True
  | .future, v, f => v = .go ∧ f = .goingTo

instance (n : Entry) (v : Verb) (f : Form) : Decidable (n.Available v f) := by
  cases n <;> unfold Entry.Available <;> infer_instance

/-- The embedded clauses an entry combines with: the movement entry needs a clause for which a
going can be a preparation. -/
def Entry.Admits : Entry → Movement → Prop
  | .movement, m => m = .possible
  | .future, _ => True

instance (n : Entry) (m : Movement) : Decidable (n.Admits m) := by
  cases n <;> unfold Entry.Admits <;> infer_instance

/-- A form with an embedded clause is licensed when one of its entries combines with the
clause. -/
def Licensed (v : Verb) (f : Form) (m : Movement) : Prop :=
  ∃ n : Entry, n.Available v f ∧ n.Admits m

instance (v : Verb) (f : Form) (m : Movement) : Decidable (Licensed v f m) :=
  inferInstanceAs (Decidable (∃ _, _))

/-- The examples are acceptable exactly where a form is licensed. -/
theorem licensed_iff (e : Example) :
    ∀ v ∈ e.verb, ∀ f ∈ e.form, ∀ m ∈ e.movement,
      (Licensed v f m ↔ e.datum.judgment = .acceptable) := by
  cases e <;> decide

end Eckardt2006
