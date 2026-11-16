module

/-!
# Aspect: basic definitions

The classificatory vocabulary of aspect follows the two components of Smith's theory. An
aspectual class, Smith's situation type, is one of Vendler's four classes or her semelfactive,
and is determined by three features: whether the situation has a natural endpoint, whether it takes time and whether
it involves change. Viewpoint is the presentation of a situation: Klein's four relations between
the topic time and the situation time together with Smith's neutral viewpoint, and at its
coarsest the opposition of perfective and imperfective. The operators that viewpoints denote are
in `Semantics/Aspect/Viewpoint.lean`.

## Implementation notes

* Smith's table of features marks states as lacking telicity and notes that the feature is
  irrelevant to static situations; `AspectualClass.telicity` gives states the value `atelic`.

## References

* [smith-1997]
* [vendler-1957]
* [dowty-1979]
* [krifka-1998]
* [klein-1994]
-/

@[expose] public section

namespace Aspect

/-! ### Aspectual class -/

/-- Whether an eventuality has a natural endpoint. An *in*-adverbial such as *in an hour* is
acceptable with the telic classes and with no other ([dowty-1979]). -/
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

/-- The aspectual classes ([dowty-1979]) are the four classes of [vendler-1957] and the
semelfactives of [smith-1997], who calls the five situation types. -/
inductive AspectualClass
  | state
  | activity
  | achievement
  | accomplishment
  | semelfactive
  deriving DecidableEq, Repr, Inhabited

namespace AspectualClass

/-- The telicity of an aspectual class. -/
def telicity : AspectualClass → Telicity
  | state | activity | semelfactive => .atelic
  | achievement | accomplishment => .telic

/-- The duration of an aspectual class. -/
def duration : AspectualClass → Duration
  | state | activity | accomplishment => .durative
  | achievement | semelfactive => .punctual

/-- The dynamicity of an aspectual class. -/
def dynamicity : AspectualClass → Dynamicity
  | state => .stative
  | activity | achievement | accomplishment | semelfactive => .dynamic

variable {c d : AspectualClass}

theorem eq_of_features (ht : c.telicity = d.telicity) (hd : c.duration = d.duration)
    (hy : c.dynamicity = d.dynamicity) : c = d := by
  revert ht hd hy
  cases c <;> cases d <;> decide

/-- Add a natural endpoint, by which an activity becomes an accomplishment and a semelfactive
an achievement. -/
def telicize : AspectualClass → AspectualClass
  | activity => accomplishment
  | semelfactive => achievement
  | c => c

theorem telicity_telicize (h : c.dynamicity = .dynamic) : c.telicize.telicity = .telic := by
  cases c <;> first | rfl | cases h

@[simp] theorem duration_telicize (c : AspectualClass) : c.telicize.duration = c.duration := by
  cases c <;> rfl

@[simp] theorem dynamicity_telicize (c : AspectualClass) :
    c.telicize.dynamicity = c.dynamicity := by
  cases c <;> rfl

end AspectualClass

/-- The incrementality of a verb's theme relation is the strongest of [krifka-1998]'s properties
it has, strictly incremental (*eat*, *draw*), incremental (*read*), or cumulative without
incrementality (*push*, *carry*). -/
inductive Incrementality
  | strict
  | incremental
  | cumulative
  deriving DecidableEq, Repr

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

end Aspect
