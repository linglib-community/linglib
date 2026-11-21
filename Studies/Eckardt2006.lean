module

public import Linglib.Logic.Modal.Defs
public import Linglib.Semantics.Aspect.Viewpoint.Basic
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
imminent, the progressive of the old entry entails the new one (`unbounded_goTo_le_beGoingTo`): the
inference that the planned event is imminent is a consequence of where the reference time lies. The
entailment holds under the present and under every tense (`beGoingTo_pure_of_unbounded_goTo`,
`diamond_goTo_le`), and in each world accessible along the modal imperfective
(`imperfective_goTo_le`). The new entry is a restriction of the prospective viewpoint
(`beGoingTo_le_prospective`) and conveys no movement (`unbounded_goTo_eq_bot`).

The old entry holds of nothing when no going prepares an event of the embedded predicate, under
every viewpoint (`diamond_runTimes_goTo_eq_bot`). A simple form has only the old entry, so it is
acceptable only where the embedded clause allows the movement interpretation, and German *gehen*,
which has no future entry, behaves in every form as the English simple forms do (`licensed_iff`).

## Implementation notes

* The progressive is the extensional `Aspect.unbounded`, the reference time within the run time of
  the event, as in the source. `imperfective_goTo_le` states the entailment for the modal
  imperfective, where an event in progress need not be completed: there the planned event follows
  the reference time in every accessible world, and in the world of evaluation only if it is
  accessible.
* The new entry has strict precedence, the reference time ending before the event starts, where the
  prospective viewpoint allows the two to meet.
* `goTo` is an event predicate and `beGoingTo` an interval property. That the progressive is no
  longer a part of the reanalysed sentence is this difference of type: no viewpoint operator applies
  to the new entry.
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
def beGoingTo (imm : NonemptyInterval T → E → Prop) (P : X → W → E → Prop) (x : X) (w : W) :
    NonemptyInterval T → Prop :=
  fun t ↦ ∃ e, t.Precedes (τ e) ∧ imm t e ∧ P x w e

theorem beGoingTo_iff :
    beGoingTo imm P x w t ↔ ∃ e, t.Precedes (τ e) ∧ imm t e ∧ P x w e := Iff.rfl

theorem beGoingTo_mono (h : ∀ t e, imm t e → imm' t e) :
    beGoingTo imm P x w ≤ beGoingTo imm' P x w :=
  fun _ ⟨e, ht, hi, hP⟩ ↦ ⟨e, ht, h _ _ hi, hP⟩

/-- The reanalysed *be going to* is a restriction of the prospective viewpoint. -/
theorem beGoingTo_le_prospective :
    beGoingTo imm P x w ≤ ViewpointType.prospective.denote (P x w) :=
  fun _ ⟨e, ht, _, hP⟩ ↦ denote_prospective_iff.2 ⟨e, le_of_lt ht, hP⟩

/-! ### From the inference to the literal content -/

section Inference

variable (hprep : ∀ e e', prepare e e' → Event.Precedes e e')
  (himm : ∀ w t e e', go x w e → prepare e e' → t ≤ τ e → imm t e')

include hprep himm

/-- (4.54): Where preparations precede what they prepare and a going in progress makes what it
prepares imminent, the progressive of movement *go* entails the reanalysed *be going to*. -/
theorem unbounded_goTo_le_beGoingTo :
    unbounded (goTo go prepare P x w) ≤ beGoingTo imm P x w := by
  intro t ht
  obtain ⟨e, hte, hgo, e', hpr, hP⟩ := unbounded_iff.1 ht
  exact ⟨e', lt_of_le_of_lt (NonemptyInterval.le_def.1 hte).2 (hprep e e' hpr),
    himm w t e e' hgo hpr hte, hP⟩

-- (4.50f) and (4.56): the entailment under the present tense.
theorem beGoingTo_pure_of_unbounded_goTo {a : T}
    (h : unbounded (goTo go prepare P x w) (.pure a)) : beGoingTo imm P x w (.pure a) :=
  unbounded_goTo_le_beGoingTo hprep himm _ h

-- (4.51) and (4.60): the entailment under every tense.
theorem diamond_goTo_le (tn : Tense) :
    ◇[toSetRel ⟦tn⟧] (fun r ↦ unbounded (goTo go prepare P x w) (.pure r)) ≤
      ◇[toSetRel ⟦tn⟧] (fun r ↦ beGoingTo imm P x w (.pure r)) :=
  diamond_mono _ fun _ hr ↦ beGoingTo_pure_of_unbounded_goTo hprep himm hr

-- The entailment in each world accessible along the modal imperfective.
theorem imperfective_goTo_le {acc : NonemptyInterval T → SetRel W W} :
    imperfective acc (goTo go prepare P x) w ≤
      fun t ↦ □[acc t] (fun v ↦ beGoingTo imm P x v t) w :=
  fun _ ht v hv ↦ unbounded_goTo_le_beGoingTo hprep himm _ (ht v hv)

end Inference

-- The reference time of a progressive is not before its own event.
theorem not_precedes_of_le {s : NonemptyInterval T} (h : t ≤ s) : ¬ t.Precedes s :=
  fun hp ↦ absurd (lt_of_le_of_lt ((NonemptyInterval.le_def.1 h).1.trans t.fst_le_snd) hp)
    (lt_irrefl _)

/-! ### What the new entry no longer conveys -/

/-- Movement *go* with an infinitive holds at no reference time, along any relation between the
reference time and the run time, when no going prepares an event of the embedded predicate. -/
theorem diamond_runTimes_goTo_eq_bot (R : SetRel (NonemptyInterval T) (NonemptyInterval T))
    (h : ∀ e e', go x w e → prepare e e' → ¬ P x w e') :
    ◇[R] (Event.runTimes (goTo go prepare P x w)) = ⊥ :=
  eq_bot_iff.2 fun _ ht ↦
    let ⟨e, _, hgo, e', hpr, hP⟩ := Event.diamond_runTimes_iff.1 ht; h e e' hgo hpr hP

theorem unbounded_goTo_eq_bot (h : ∀ e, ¬ go x w e) :
    unbounded (goTo go prepare P x w) = ⊥ :=
  diamond_runTimes_goTo_eq_bot _ fun e _ hgo _ ↦ (h e hgo).elim

-- A time at which something is going to happen though nothing moves.
theorem beGoingTo_pure :
    beGoingTo (E := NonemptyInterval ℕ) (fun _ _ ↦ True)
      (fun (_ _ : Unit) e ↦ e = .pure 1) () () (.pure 0) :=
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
