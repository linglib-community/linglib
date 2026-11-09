module

public import Linglib.Fragments.English.Verbs.Basic

/-!
# English implicative and control verbs

This file defines the English implicative verbs *manage*, *fail*, *try*, *remember*, *forget*
and *neglect*, the control verbs *persuade* and *promise*, the raising verb *seem*, and the
prerequisite implicatives *dare*, *bother*, *hesitate*, *venture*, *condescend* and *happen*,
with the entailment each carries from its complement.

## References

* [bruening-2021]
* [karttunen-1971]
* [landau-2015]
* [solstad-bott-2024]
-/

@[expose] public section

namespace English.Verbs

open ArgumentStructure Aspect Data.VerbClasses

/-! ### Implicative / Control -/

/-- "manage" — a positive implicative; "managed to VP" entails "VP", and on the traditional
    analysis the agentive subject controls the complement.
    -/
def manage : Verb where
  morphs := [.root "manage"]
  levin := none
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- "fail" — a negative implicative; "failed to VP" entails "not VP". -/
def fail : Verb where
  morphs := [.root "fail"]
  levin := none
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .negative, .some .positive⟩

/-- "try" — subject control, no entailment -/
def try_ : Verb where
  morphs := [.root "try"]
  levin := some Levin1993.Index.«try»
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .activity
  passivizable := false

/-- "persuade" — object control, "persuade X to VP" with X the agent of VP. A psychological
    attitude verb whose object comes to form an intention; it projects the AUTHOR coordinate,
    so control is obligatorily *de se* ([landau-2015] table (36)). -/
def persuade : Verb where
  morphs := [.root "persuade"]
  levin := none
  valency := .ofFrame toInfinitive.withObject (controller := some 1)
  vendlerClass := some .accomplishment
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- "promise" — subject control across an object, "promise X to VP". A desiderative attitude
    verb whose subject commits to a future action; [landau-2015] (5c) classifies it as
    desiderative, hence logophoric control. Its direct object may be implicit in the double
    object frame only, a definite (*Promise me!*; [bruening-2021]). -/
def promise : Verb where
  morphs := [.root "promise"]
  levin := some Levin1993.Index.promise
  valency := .of
    [(toInfinitive, [0, 1]),
     (toInfinitive.withObject, [0, 2, 1]),
     (ArgumentFrame.np_np, [0, 2, 1]),
     (ArgumentFrame.np_pp (some Adpositions.to_) (some .dat), [0, 1, 2]),
     (ArgumentFrame.np_np.leaveImplicit 1 (some .def), [0, 2, 1])]
    (controllers := [some 0, some 0])
  vendlerClass := some .achievement
  opaqueContext := true
  attitude := some (.preferential .positive)

/-- "remember" — implicative with infinitival ("remember to call") -/
def remember : Verb where
  morphs := [.root "remember"]
  levin := some Levin1993.Index.remember
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- *forget* with an infinitive is one of [karttunen-1971]'s negative implicatives, so *forgot
    to lock the door* entails *did not lock the door*. The factive sense that takes a finite
    clause, a gerund or a question is `forget_rog`; [williams-2025] takes the two senses to be one
    verb whose plain infinitive carries a covert modal. -/
def forget : Verb where
  morphs := [.root "forget"]
  levin := none
  past := "forgot"
  pastPart := "forgotten"
  doubling := true
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .negative, .some .positive⟩

/-- *neglect* is listed with *forget* and *fail* among [karttunen-1971]'s negative
    implicatives, so neglecting to lock the door entails not locking it. -/
def neglect : Verb where
  morphs := [.root "neglect"]
  levin := none
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .negative, .some .positive⟩

/-! ### Raising -/

/-- The frame of an experiencer *to*-phrase and an infinitive, *seem to his parents to be
writing*. -/
def experiencerFrame : ArgumentFrame :=
  { toInfinitive with
    complements := .adposition (some Adpositions.to_) (some .dat) :: toInfinitive.complements }

/-- *seem* is a raising verb, raising into a subject that is no participant of its own. With an
    experiencer it reports the experiencer's view, a doxastic attitude ([wurmbrand-2014] (70)). -/
def seem : Verb where
  morphs := [.root "seem"]
  levin := none
  valency := .ofLinks [(toInfinitive, [none, some 0]), (experiencerFrame, [none, some 1, some 0])]
    (controls := [some .external, some .external])
  vendlerClass := some .state
  passivizable := false
  readings := [{ frame := experiencerFrame, attitude := some (.doxastic .doxastic) }]

/-! ### Prerequisite implicatives -/

/-! Implicatives whose complement is entailed through a prerequisite the verb names,
[nadathur-2023-implicatives]'s causal analysis of *manage*, *dare* and their kin; the
occasion verbs of [solstad-bott-2024] (*thank*, *criticize*, *congratulate*) presuppose an
occasioning eventuality in a parallel way the authors draw and then set apart. -/

/-- "dare" — a positive implicative whose prerequisite presupposition is courage. "Ana dared
    to enter the cave" entails "Ana entered the cave" and presupposes that a daring action was
    required for the complement to be realized ([nadathur-2023-implicatives] §5.2, ex. 3–4,
    26). -/
def dare : Verb where
  morphs := [.root "dare"]
  levin := none
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- "bother" — a positive implicative whose prerequisite presupposition is engagement. "He
    bothered to answer" entails "He answered" and presupposes that apathy had to be overcome
    ([nadathur-2023-implicatives] §2, ex. 10, 28). -/
def bother : Verb where
  morphs := [.root "bother"]
  levin := some Levin1993.Index.bother
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- "hesitate" — polarity-reversing one-way implicative.
    "Amira hesitated to drink a beer" ↛ "Amira did not drink a beer."
    "Amira did not hesitate to drink a beer" → "Amira drank a beer."
    The paper does not explicitly name the prerequisite for *hesitate*;
    it is treated as a polarity-reversing analog of *dare*
    ([nadathur-2023-implicatives] §6.4, ex. 45–47). -/
def hesitate : Verb where
  morphs := [.root "hesitate"]
  levin := some Levin1993.Index.hesitate
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .activity
  passivizable := false
  implicative := ⟨⊥, .some .positive⟩

/-- *venture* is a positive implicative among [karttunen-1971]'s implicative predicates, so
    venturing to speak entails speaking. -/
def venture : Verb where
  morphs := [.root "venture"]
  levin := none
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- *condescend* is a positive implicative among [karttunen-1971]'s implicative predicates, so
    condescending to help entails helping. -/
def condescend : Verb where
  morphs := [.root "condescend"]
  levin := none
  valency := .ofFrame toInfinitive (controller := some 0)
  vendlerClass := some .achievement
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

/-- *happen* is a raising verb and a positive implicative among [karttunen-1971]'s implicative
    predicates, so happening to see Mary entails seeing her. Its subject gets no θ-role from it,
    as *It happened to rain* shows. -/
def happen : Verb where
  morphs := [.root "happen"]
  levin := some Levin1993.Index.happen
  valency := .ofLinks [(toInfinitive, [none, some 0])] (controls := [some .external])
  passivizable := false
  implicative := ⟨.some .positive, .some .negative⟩

end English.Verbs
