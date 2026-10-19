module

/-!
# Aspect: basic definitions

This file defines the classificatory vocabulary of aspect, following the two components of
Smith's theory. Situation type classifies an eventuality by three binary features: whether it
has a natural endpoint (`Telicity`), whether it takes time (`Duration`) and whether it involves
change (`Dynamicity`). The situation types are the four classes of Vendler together with
Smith's semelfactives (`VendlerClass`), each determined by its features
(`VendlerClass.eq_of_features`). The aspectual shifts of compositional coercion change one
feature of a situation type (`VendlerClass.telicize` and its siblings), and Dowty's adverbial
and progressive diagnostics are functions of the features (`forXPrediction`, `inXPrediction`,
`progressivePrediction`), and the two tests for the Slavic perfective and imperfective are a
function of the viewpoint (`viewpointPrediction`). Viewpoint is the
presentation of a situation, Klein's four relations between the topic time and the situation
time together with Smith's neutral viewpoint (`ViewpointType`), and at its coarsest the
opposition of perfective and imperfective (`Perfectivity`). A language's aspect morphemes are
entered with the viewpoint each marks in `Semantics/Aspect/Marker.lean`, and the operators that
viewpoints denote are in `Semantics/Aspect/Viewpoint.lean`.

## Main definitions

* `Aspect.VendlerClass`: the five situation types, with their features and shifts.
* `Aspect.Incrementality`: the incrementality classes of a verb's theme relation.
* `Aspect.DiagnosticResult`: the outcome of a diagnostic, with the *for*-adverbial,
  *in*-adverbial and progressive tests as functions of a situation type.
* `Aspect.ViewpointType`, `Aspect.Perfectivity`: the viewpoints.
* `Aspect.viewpointPrediction`: the phase-verb and present-tense tests as a function of the
  opposition of perfective and imperfective.

## References

* [smith-1997]
* [vendler-1957]
* [dowty-1979]
* [krifka-1998]
* [klein-1994]
* [borik-2006]
-/

@[expose] public section

namespace Aspect

/-! ### Situation type -/

/-- Whether an eventuality has a natural endpoint. -/
inductive Telicity
  | telic
  | atelic
  deriving DecidableEq, Repr, Inhabited

/-- Whether an eventuality takes time or is instantaneous. -/
inductive Duration
  | durative
  | punctual
  deriving DecidableEq, Repr, Inhabited

/-- Whether an eventuality involves change. -/
inductive Dynamicity
  | dynamic
  | stative
  deriving DecidableEq, Repr, Inhabited

/-- The five situation types are the four classes of [vendler-1957] and the semelfactives of
[smith-1997]. -/
inductive VendlerClass
  | state
  | activity
  | achievement
  | accomplishment
  | semelfactive
  deriving DecidableEq, Repr, Inhabited

namespace VendlerClass

/-- The telicity of a situation type. -/
def telicity : VendlerClass → Telicity
  | state | activity | semelfactive => .atelic
  | achievement | accomplishment => .telic

/-- The duration of a situation type. -/
def duration : VendlerClass → Duration
  | state | activity | accomplishment => .durative
  | achievement | semelfactive => .punctual

/-- The dynamicity of a situation type. -/
def dynamicity : VendlerClass → Dynamicity
  | state => .stative
  | activity | achievement | accomplishment | semelfactive => .dynamic

end VendlerClass

namespace VendlerClass

variable {c d : VendlerClass}

/-- A situation type is determined by its three features. -/
theorem eq_of_features (ht : c.telicity = d.telicity) (hd : c.duration = d.duration)
    (hy : c.dynamicity = d.dynamicity) : c = d := by
  revert ht hd hy
  cases c <;> cases d <;> decide

/-- Add a natural endpoint, by which an activity becomes an accomplishment and a semelfactive
an achievement. -/
def telicize : VendlerClass → VendlerClass
  | activity => accomplishment
  | semelfactive => achievement
  | c => c

/-- Remove the natural endpoint, the effect of the progressive. -/
def atelicize : VendlerClass → VendlerClass
  | accomplishment => activity
  | achievement => semelfactive
  | c => c

/-- Stretch a punctual eventuality over time, the iterative reading. -/
def duratize : VendlerClass → VendlerClass
  | achievement => accomplishment
  | semelfactive => activity
  | c => c

theorem telicity_telicize (h : c.dynamicity = .dynamic) : c.telicize.telicity = .telic := by
  cases c <;> first | rfl | cases h

@[simp] theorem duration_telicize (c : VendlerClass) : c.telicize.duration = c.duration := by
  cases c <;> rfl

@[simp] theorem dynamicity_telicize (c : VendlerClass) :
    c.telicize.dynamicity = c.dynamicity := by
  cases c <;> rfl

@[simp] theorem telicity_atelicize (c : VendlerClass) : c.atelicize.telicity = .atelic := by
  cases c <;> rfl

@[simp] theorem duration_atelicize (c : VendlerClass) : c.atelicize.duration = c.duration := by
  cases c <;> rfl

@[simp] theorem dynamicity_atelicize (c : VendlerClass) :
    c.atelicize.dynamicity = c.dynamicity := by
  cases c <;> rfl

@[simp] theorem duration_duratize (c : VendlerClass) : c.duratize.duration = .durative := by
  cases c <;> rfl

@[simp] theorem telicity_duratize (c : VendlerClass) : c.duratize.telicity = c.telicity := by
  cases c <;> rfl

@[simp] theorem dynamicity_duratize (c : VendlerClass) :
    c.duratize.dynamicity = c.dynamicity := by
  cases c <;> rfl

end VendlerClass

/-- The incrementality of a verb's theme relation is the strongest of [krifka-1998]'s properties
it has, strictly incremental (*eat*, *draw*), incremental (*read*), or cumulative without
incrementality (*push*, *carry*). -/
inductive Incrementality
  | strict
  | incremental
  | cumulative
  deriving DecidableEq, Repr

/-! ### Diagnostics

The adverbial and progressive tests of [dowty-1979], as functions of the three features: a
*for*-adverbial measures an atelic durative eventuality and coerces a telic or punctual one into
repetition or iteration; an *in*-adverbial needs a culmination; the progressive needs internal
stages, reads an achievement through its preliminary stages and a semelfactive as iterated. -/

/-- The outcome of a diagnostic is acceptable, unacceptable, degraded, or acceptable under a
meaning shift. -/
inductive DiagnosticResult
  | accept
  | reject
  | marginal
  | coerced
  deriving DecidableEq, Repr

/-- The *for*-adverbial test. -/
def forXPrediction (c : VendlerClass) : DiagnosticResult :=
  match c.telicity, c.duration with
  | .atelic, .durative => .accept
  | .telic, .punctual => .reject
  | _, _ => .coerced

/-- The *in*-adverbial test. -/
def inXPrediction (c : VendlerClass) : DiagnosticResult :=
  if c.telicity = .telic then .accept else .reject

/-- The progressive test. -/
def progressivePrediction (c : VendlerClass) : DiagnosticResult :=
  match c.dynamicity, c.duration, c.telicity with
  | .stative, _, _ => .reject
  | .dynamic, .durative, _ => .accept
  | .dynamic, .punctual, .telic => .marginal
  | .dynamic, .punctual, .atelic => .coerced

theorem inXPrediction_eq_accept_iff (c : VendlerClass) :
    inXPrediction c = .accept ↔ c.telicity = .telic := by
  cases c <;> decide

theorem forXPrediction_eq_accept_iff (c : VendlerClass) :
    forXPrediction c = .accept ↔ c.telicity = .atelic ∧ c.duration = .durative := by
  cases c <;> decide

theorem progressivePrediction_eq_accept_iff (c : VendlerClass) :
    progressivePrediction c = .accept ↔ c.duration = .durative ∧ c.dynamicity = .dynamic := by
  cases c <;> decide

/-! ### Viewpoint -/

/-- The viewpoints are the four relations of [klein-1994] between the topic time and the situation
time, and the neutral viewpoint of [smith-1997], the default in the absence of aspect
morphology. -/
inductive ViewpointType
  | imperfective
  | perfective
  | perfect
  | prospective
  | neutral
  deriving DecidableEq, Repr, Inhabited

/-- The opposition of perfective and imperfective is viewpoint aspect at its coarsest, the right
granularity where the fact at issue is that the perfective requires actualization and the
imperfective does not, or where the opposition is lexically encoded, as in `Verb.perfectivity`. -/
inductive Perfectivity
  | perfective
  | imperfective
  deriving DecidableEq, Repr, Inhabited

/-- The tests for the Slavic perfective and imperfective [borik-2006]: the infinitival complement
of a phase verb such as *begin*, *continue* or *finish* is imperfective, and the present-tense
form of a perfective has no actual present reading, referring to a later time. Both tests accept
an imperfective form and reject a perfective one. -/
def viewpointPrediction : Perfectivity → DiagnosticResult
  | .imperfective => .accept
  | .perfective => .reject

theorem viewpointPrediction_eq_accept_iff (p : Perfectivity) :
    viewpointPrediction p = .accept ↔ p = .imperfective := by
  cases p <;> decide

end Aspect
