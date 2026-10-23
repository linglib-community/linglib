module

public import Linglib.Core.Order.Interval.Basic
public import Linglib.Semantics.Tense.Defs
public import Linglib.Syntax.Minimalist.Clause.Size
public import Linglib.Data.Examples.Wurmbrand2014

/-!
# Wurmbrand (2014): Tense and Aspect in English Infinitives

This file formalizes [wurmbrand-2014]'s account of the temporal composition of English
infinitival complements. Three classes are distinguished by whether a bare, nonprogressive
verb phrase can be episodic: future infinitives allow it, propositional attitude infinitives
never do, and tenseless simultaneous infinitives allow it depending on the matrix tense
(`InfinitivalTenseClass`). The distribution is derived from viewpoint aspect. Perfective
aspect includes the event time in the reference time and imperfective the reverse
(`Perfective`), and an episodic eventive predicate occupies an extended interval, so
perfective fails whenever the reference time is an instant (`not_perfective_of_isPoint`).
Each class fixes the embedded reference time (`ReferenceTime`): the future modal *woll* shifts
it to an unrestricted interval after the evaluation time, a propositional attitude imposes the
holder's NOW, an instant, and a tenseless simultaneous infinitive inherits the matrix reference
time, an instant under present tense and an extended interval under past. The three rows of
the paper's table follow (`Episodic`), and a verb ambiguous between classes, like *seem*, is
episodic exactly when one of its classes is (`Verb.Episodic`).

Future infinitives are tenseless: finite *will* is present tense plus *woll* and *would* is
past plus *woll* (`Composition`), so finite future is absolute while infinitival future is
relative to the matrix event (`infinitival_relative`), and infinitives are invisible to the
sequence-of-tense rule, whose local tense feature skips them (`localTense`): a past under an
infinitive under past deletes, a past under *will* does not, and a silent *would* in the
infinitive would wrongly license deletion under a *will* matrix (`silent_would_wrong`).

## Implementation notes

Times are the nonempty intervals of a linear order; an instant is an interval whose endpoints
coincide. The evaluation time of *woll* and the attitude holder's NOW are one instant
parameter, and adverbials that restrict a reference time to an instant fall under the same
lemma as the NOW. The obligatory deletion of *would*'s past is taken as the paper does, as a
lexical requirement.

## References

* [wurmbrand-2014]
* [ogihara-1996]
* [abusch-1988]
* [wurmbrand-2001]
* [landau-2000]
-/

@[expose] public section

namespace Wurmbrand2014

open Semantics

/-- The three classes of infinitival complement by tense behaviour. Future irrealis infinitives,
*decide*, *want* and *plan*, are tenseless with *woll* and future-oriented; propositional
infinitives, *believe* and *claim*, are anchored to the attitude holder's now; restructuring
infinitives, *try*, *begin* and *seem*, have no attitude holder and take the matrix reference
time. -/
inductive InfinitivalTenseClass
  | futureIrrealis
  | propositional
  | restructuring
  deriving DecidableEq, Repr, Inhabited

/-- The structural size of each class, the modal layer of *woll* for a future irrealis
infinitive, a TP for a propositional one and a bare vP for a restructuring one, the modal and
tense layers sharing a level of the functional sequence. -/
def InfinitivalTenseClass.complementSize : InfinitivalTenseClass → Minimalist.ComplementSize
  | .futureIrrealis => .modP
  | .propositional => .tP
  | .restructuring => .vP

open Tense Minimalist

/-! ### Viewpoint aspect -/

section Aspect

variable {T : Type*} [LinearOrder T]

/-- Perfective aspect includes the event time in the reference time. -/
def Perfective (e r : NonemptyInterval T) : Prop := e ≤ r

/-- Imperfective aspect includes the reference time in the event time. -/
def Imperfective (e r : NonemptyInterval T) : Prop := r ≤ e

theorem not_perfective_of_isPoint {e r : NonemptyInterval T} (he : ¬ e.IsPoint)
    (hr : r.IsPoint) : ¬ Perfective e r := by
  intro h
  rw [Perfective, NonemptyInterval.le_def] at h
  exact he (le_antisymm e.fst_le_snd (h.2.trans (hr.symm.le.trans h.1)))

theorem imperfective_pure_of_mem {e : NonemptyInterval T} {t : T} (h : t ∈ e) :
    Imperfective e (NonemptyInterval.pure t) := by
  rw [Imperfective, NonemptyInterval.le_def]
  exact NonemptyInterval.mem_def.mp h

/-! ### The reference time of an infinitive -/

variable (matrixR : NonemptyInterval T) (now : T)

/-- The reference time each class assigns the embedded aspect, given the matrix reference
time and the evaluation instant: after *woll*, any interval after the evaluation time; under a
propositional attitude, the holder's NOW; in a tenseless simultaneous infinitive, the matrix
reference time. -/
def ReferenceTime : InfinitivalTenseClass → NonemptyInterval T → Prop
  | .futureIrrealis, r => now < r.fst
  | .propositional, r => r = NonemptyInterval.pure now
  | .restructuring, r => r = matrixR

/-- A bare episodic verb phrase is available when some reference time of the class includes
an extended event time. -/
def Episodic (c : InfinitivalTenseClass) : Prop :=
  ∃ r, ReferenceTime matrixR now c r ∧
    ∃ e : NonemptyInterval T, ¬ e.IsPoint ∧ Perfective e r

theorem episodic_futureIrrealis [NoMaxOrder T] : Episodic matrixR now .futureIrrealis := by
  obtain ⟨a, ha⟩ := exists_gt now
  obtain ⟨b, hb⟩ := exists_gt a
  exact ⟨⟨(a, b), hb.le⟩, ha, ⟨(a, b), hb.le⟩, hb.ne, le_rfl⟩

theorem not_episodic_propositional : ¬ Episodic matrixR now .propositional := by
  rintro ⟨r, rfl, e, he, h⟩
  exact not_perfective_of_isPoint he (show (NonemptyInterval.pure now).IsPoint from rfl) h

theorem episodic_restructuring_iff :
    Episodic matrixR now .restructuring ↔ ¬ matrixR.IsPoint := by
  constructor
  · rintro ⟨r, rfl, e, he, h⟩ hp
    exact not_perfective_of_isPoint he hp h
  · exact fun h ↦ ⟨matrixR, rfl, matrixR, h, le_rfl⟩

/-! ### Verbs -/

/-- The infinitive-taking verbs of the paper's table. -/
inductive Verb where
  | decide
  | want
  | promise
  | expect
  | claim
  | believe
  | try_
  | begin_
  | manage
  | seem
  deriving DecidableEq, Repr

/-- The classes a verb's infinitive may belong to. *Expect* is future or, as a belief,
propositional; *seem* is tenseless simultaneous or, with an attitude holder, propositional. -/
def Verb.classes : Verb → List InfinitivalTenseClass
  | .decide | .want | .promise => [.futureIrrealis]
  | .expect => [.futureIrrealis, .propositional]
  | .claim | .believe => [.propositional]
  | .try_ | .begin_ | .manage => [.restructuring]
  | .seem => [.restructuring, .propositional]

/-- A verb's infinitive has an episodic reading when one of its classes does. -/
def Verb.Episodic (v : Verb) : Prop :=
  ∃ c ∈ v.classes, Wurmbrand2014.Episodic matrixR now c

theorem believe_not_episodic : ¬ Verb.believe.Episodic matrixR now := by
  rintro ⟨c, hc, h⟩
  simp only [Verb.classes, List.mem_singleton] at hc
  exact not_episodic_propositional matrixR now (hc ▸ h)

theorem seem_episodic_iff : Verb.seem.Episodic matrixR now ↔ ¬ matrixR.IsPoint := by
  constructor
  · rintro ⟨c, hc, h⟩
    simp only [Verb.classes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact (episodic_restructuring_iff matrixR now).mp h
    · exact absurd h (not_episodic_propositional matrixR now)
  · exact fun h ↦ ⟨.restructuring, by simp [Verb.classes],
      (episodic_restructuring_iff matrixR now).mpr h⟩

theorem decide_episodic [NoMaxOrder T] : Verb.decide.Episodic matrixR now :=
  ⟨.futureIrrealis, by simp [Verb.classes], episodic_futureIrrealis matrixR now⟩

end Aspect

/-! ### Temporal composition -/

/-- The temporal composition of a clause is an optional tense feature together with whether the
future modal *woll* is present. -/
structure Composition where
  tense : Option (Finset Ordering)
  woll : Bool
  deriving DecidableEq

/-- Finite *will* is present tense plus *woll*. -/
def will : Composition := ⟨some ⟦present⟧, true⟩

/-- Finite *would* is past tense plus *woll*. -/
def would : Composition := ⟨some ⟦past⟧, true⟩

/-- An infinitive has no tense, with or without *woll*. -/
def infinitive (woll : Bool) : Composition := ⟨none, woll⟩

/-- The composition of each class is tenseless, with *woll* in the future class only. -/
def composition : InfinitivalTenseClass → Composition
  | .futureIrrealis => infinitive true
  | .propositional | .restructuring => infinitive false

theorem woll_iff_modP (c : InfinitivalTenseClass) :
    (composition c).woll = true ↔ c.complementSize = .modP := by
  cases c <;> decide

section Future

variable {T : Type*} [LinearOrder T]

/-- A composition with *woll* locates its event after the utterance time when present tense is
present and after the evaluation time otherwise. -/
def Composition.Locates (c : Composition) (utterance eval e : T) : Prop :=
  c.woll = true ∧ if c.tense = some ⟦present⟧ then utterance < e else eval < e

theorem will_absolute {utterance eval e : T} (h : will.Locates utterance eval e) :
    utterance < e := by
  simpa [will, Composition.Locates] using h.2

theorem infinitival_relative [DenselyOrdered T] {utterance eval : T} (h : eval < utterance) :
    ∃ e, (infinitive true).Locates utterance eval e ∧ e < utterance := by
  obtain ⟨e, h₁, h₂⟩ := exists_between h
  exact ⟨e, ⟨rfl, by simpa [infinitive] using h₁⟩, h₂⟩

end Future

/-! ### Sequence of tense -/

/-- The local tense feature of an embedded tense is the nearest tense feature above it,
infinitives contributing none. -/
def localTense : List (Option (Finset Ordering)) → Option (Finset Ordering)
  | [] => none
  | some f :: _ => some f
  | none :: rest => localTense rest

/-- Ogihara's rule lets an embedded tense delete when its local tense feature is the same
feature. -/
def sotApplies (above : List (Option (Finset Ordering))) (embedded : Finset Ordering) : Bool :=
  match localTense above with
  | some m => decide (m = embedded)
  | none => false

theorem sot_will_blocks : sotApplies [will.tense, some ⟦past⟧] ⟦past⟧ = false := by decide

theorem sot_infinitive_transparent :
    sotApplies [(infinitive true).tense, some ⟦past⟧] ⟦past⟧ = true := by
  decide

theorem sot_would : sotApplies [would.tense, some ⟦past⟧] ⟦past⟧ = true := by decide

theorem sot_will_infinitive : sotApplies [(infinitive true).tense, will.tense] ⟦past⟧ = false := by
  decide

theorem silent_would_wrong : sotApplies [would.tense, will.tense] ⟦past⟧ = true := by decide

/-- *would*'s past must delete: it is licensed only below a past. -/
def WouldLicensed (above : List (Option (Finset Ordering))) : Prop := sotApplies above ⟦past⟧ = true

instance : DecidablePred WouldLicensed := fun _ ↦ inferInstanceAs (Decidable (_ = true))

theorem would_licensing : ¬ WouldLicensed [will.tense] ∧ WouldLicensed [some ⟦past⟧] := by decide

end Wurmbrand2014
