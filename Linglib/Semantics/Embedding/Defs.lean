/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Logic.Natural.ImplicationSignature
public import Linglib.Semantics.Embedding.Attitude
public import Linglib.Semantics.Presupposition.Trigger
public import Linglib.Syntax.Category.Verb.ArgumentFrame.Basic

/-!
# Clause-embedding predicates

A predicate that embeds a clause, whatever its word class, has properties that concern its
complement: *know* and *be aware* are factive, *manage* implies its complement in a positive
context and the complement's negation in a negative one, *believe* and *hope* express attitudes of
different kinds. Some of these properties vary with the complement. Buryat *hanaxa* 'think' is
translated 'remember' with a nominalized clause, which it presupposes, and not with a bare one. An
entry therefore records the properties of the predicate together with the readings of single
frames, each of which overrides some of them, and the predicate on a frame is the entry with the
reading of that frame applied.

## Main definitions

* `Clause.Embedding`: what a predicate does with a clausal complement.
* `Clause.Embedding.Reading`: the properties that one frame overrides.
* `Clause.Embedding.on`: the predicate on a frame.
* `Clause.Embedding.IsFactive`, `Clause.Embedding.IsVeridical`, `Clause.Embedding.IsTrigger`:
  the predicate is recorded as factive, entails its complement, triggers a presupposition.

## Main results

* `Clause.Embedding.on_eq_self_iff`: the predicate is the same on a frame as off it exactly when
  it has no readings.

## Implementation notes

Whether a predicate triggers a presupposition is derived, not recorded. A factive presupposes its
complement, and an implicative presupposes that what it asserts is a condition for its complement;
veridicality is an entailment and does not make a predicate factive.

The predicate on a frame is again an entry, with no readings, so that every property of entries is
a property of a predicate on a frame.

## References

* [noonan-2007]
* [karttunen-1971]
* [karttunen-1971b]
* [nairn-condoravdi-karttunen-2006]
* [bondarenko-2022]
* [wurmbrand-lohninger-2023]
-/

@[expose] public section

open NaturalLogic (ImplicationSignature)

namespace Clause.Embedding

/-- The reading of a predicate on one frame overrides the predicate's attitude, factivity and
opacity there, `none` leaving the predicate's own, and records the sort of the frame's complement.
Buryat *hanaxa* 'think' has two ([bondarenko-2022] §4.4.3). -/
structure Reading where
  /-- The reading applies to every frame of the predicate at most this one, in the order on
  `ArgumentFrame`. -/
  frame : ArgumentFrame
  /-- Frame-conditioned attitude override. -/
  attitude : Option Attitude := none
  /-- Frame-conditioned opacity override. -/
  opaqueContext : Option Bool := none
  /-- Frame-conditioned factivity override. -/
  factivity : Option Presupposition.Factivity := none
  /-- The semantic sort of the complement on this frame ([wurmbrand-lohninger-2023]). -/
  size : Option Size := none
  deriving DecidableEq, Repr

end Clause.Embedding

namespace Clause

/-- What a predicate does with a clausal complement. -/
structure Embedding where
  /-- The [karttunen-1971b] factivity class a source gives a factive predicate. `none` records no
  class: an entry that says nothing is not thereby non-factive. -/
  factivity : Option Presupposition.Factivity := none
  /-- The [nairn-condoravdi-karttunen-2006] implication signature of the predicate, the polarity
  of the complement it implies in a positive and in a negative context; `⊥` for a predicate that
  implies nothing. -/
  implicative : ImplicationSignature := ⊥
  /-- Does the predicate create an opaque context for its complement? -/
  opaqueContext : Bool := false
  /-- The attitude the predicate expresses, doxastic or preferential, if it is an attitude
  predicate. -/
  attitude : Option Attitude := none
  /-- The readings of single frames, the first that applies to a frame taking precedence. -/
  readings : List Embedding.Reading := []
  deriving DecidableEq, Repr

namespace Embedding

/-- The predicate is recorded as factive: it carries a [karttunen-1971b] factivity class. Its
negation says only that no class is recorded. -/
def IsFactive (e : Embedding) : Prop := e.factivity ≠ none

instance : DecidablePred IsFactive := fun _ ↦ inferInstanceAs (Decidable (_ ≠ _))

/-- The predicate triggers a presupposition about its complement when it is factive or
implicative. -/
def IsTrigger (e : Embedding) : Prop := e.IsFactive ∨ e.implicative ≠ ⊥

instance : DecidablePred IsTrigger := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- The predicate is a veridical attitude, entailing its complement: it is doxastic, and factive
or over epistemic alternatives. -/
def IsVeridical (e : Embedding) : Prop := ∃ a ∈ e.attitude, a.IsVeridical e.factivity

instance : DecidablePred IsVeridical := fun e ↦
  inferInstanceAs (Decidable (∃ a ∈ e.attitude, a.IsVeridical e.factivity))

/-- The reading that applies to frame `fr` is the first whose frame `fr` is at most. -/
def reading? (e : Embedding) (fr : ArgumentFrame) : Option Reading :=
  e.readings.find? fun r ↦ decide (fr ≤ r.frame)

/-- The predicate on frame `fr` has each property from the reading that applies to `fr` where
that reading gives one, and the predicate's own otherwise. -/
@[simps]
def on (e : Embedding) (fr : ArgumentFrame) : Embedding where
  factivity := ((e.reading? fr).bind (·.factivity)).or e.factivity
  implicative := e.implicative
  opaqueContext := ((e.reading? fr).bind (·.opaqueContext)).getD e.opaqueContext
  attitude := ((e.reading? fr).bind (·.attitude)).or e.attitude
  readings := []

variable (e : Embedding) (fr fr' : ArgumentFrame)

@[simp] theorem on_on : (e.on fr).on fr' = e.on fr := rfl

/-- The predicate on a frame is the predicate itself exactly when it has no readings. -/
theorem on_eq_self_iff : e.on fr = e ↔ e.readings = [] :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ by cases e; subst h; rfl⟩

end Embedding

end Clause
