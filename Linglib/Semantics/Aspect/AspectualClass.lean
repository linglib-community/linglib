module

public import Mathlib.Tactic.DeriveFintype

/-!
# Aspectual classes

An aspectual class, Smith's situation type, is one of Vendler's four classes or her semelfactive.
It is determined by three features: whether the situation has a natural endpoint, `Telicity`,
whether it takes time, `Duration`, and whether it involves change, `Dynamicity`
(`AspectualClass.eq_of_features`). The incrementality of a verb's theme relation is the strongest
of Krifka's properties that the relation has.

## Implementation notes

* Smith's table of features marks states as lacking telicity and notes that the feature is
  irrelevant to static situations; `AspectualClass.telicity` gives states the value `atelic`.

## References

* [smith-1997]
* [vendler-1957]
* [dowty-1979]
* [krifka-1998]
-/

@[expose] public section

namespace Aspect

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

end AspectualClass

/-- The incrementality of a verb's theme relation is the strongest of [krifka-1998]'s properties
it has, strictly incremental (*eat*, *draw*), incremental (*read*), or cumulative without
incrementality (*push*, *carry*). -/
inductive Incrementality
  | strict
  | incremental
  | cumulative
  deriving DecidableEq, Repr

end Aspect
