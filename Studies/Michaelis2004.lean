/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Syntax.ConstructionGrammar.Composition
public import Linglib.Semantics.Aspect.Defs

/-!
# Michaelis (2004): Type Shifting in Construction Grammar

This file formalizes the account of aspectual coercion without interpolated coercion
operators in [michaelis-2004]. Constructions denote semantic types, and the override
principle resolves a mismatch between a lexical item and its morphosyntactic context in
favour of the construction: concord constructions denote the type they select, shift
constructions a different one, both shifting implicitly through the override and only shift
constructions shifting explicitly. The reconciliation operators, inchoative addition, onset
selection, and conformity to an activity (`inchoativeAddition`, `onsetSelection`,
`conformToActivity`), the frame adverbial as a concord construction and the progressive as a
shift construction, the two readings of an activity under a frame adverbial
(`frame_adverbial_activity_ambiguity`), and the stativity of progressive predications
whatever the complement's Aktionsart (`progressive_stativizes`) are stated.

## TODO

Figure 6 is checked against the paper; the other example, figure, and table locators are
transcribed from an earlier version of this file and are UNVERIFIED.

## References

* [michaelis-2004]
-/

@[expose] public section

namespace Michaelis2004

open ConstructionGrammar
open Aspect

/-! ### Reconciliation operators

The override principle repairs a type mismatch by one of the paper's
reconciliation operations on the input's aspectual representation. -/

/-- The addition operator under inchoative construal (§5.1.2): a change
is added to the causal representation, so a state yields the achievement
of its onset — "They were bored in a minute" denotes the onset of
boredom — and an activity a bounded accomplishment. Other types are left
as they are. -/
def inchoativeAddition (p : VendlerClass) : VendlerClass :=
  if p.dynamicity = .stative then .achievement
  else if p = .activity then .accomplishment
  else p

/-- The selection operator (§5.1.2): the onset phase of a durative
situation is selected, an achievement — ex. (41)'s reading on which the
frame measures the delay before the program began to air. -/
def onsetSelection (p : VendlerClass) : VendlerClass :=
  if p.duration = .durative then .achievement else p

/-- The reconciliation operators available to the frame adverbial. -/
def reconciliation : List (VendlerClass → VendlerClass) :=
  [inchoativeAddition, onsetSelection]

/-- The progressive's complement is inherently processual (§5.2.1): the
override conforms any input to the activity type — states via the
addition of `hold` and an effector to their causal representation, telic
events via their processual construal. -/
def conformToActivity : VendlerClass → VendlerClass :=
  fun _ ↦ .activity

/-! ### The frame adverbial construction (Figure 5, concord) -/

/-- The frame adverbial's composition rule: the `within` frame demands a
telic event and the construct denotes that same type. -/
def frameAdverbialRule : CompositionRule VendlerClass
  | [p] => if p.telicity = .telic then some p else none
  | _ => none

/-- The frame adverbial construction (Figure 5): an *in*-headed adjunct
added to the verbal valence. -/
def frameAdverbial : Construction (CompositionRule VendlerClass) :=
  { form :=
      [ { filler := .open_ .VERB, isHead := true }
      , { filler := .fixed "in" }
      , { filler := .open_ .NOUN } ]
  , meaning := frameAdverbialRule }

/-! ### The progressive construction (Figure 6, shift) -/

/-- The progressive's composition rule: an activity complement yields the
state holding during the activity's interval, by selection of an
intermediate rest in its temporal representation. -/
def progressiveRule : CompositionRule VendlerClass
  | [p] => if p = .activity then some .state else none
  | _ => none

/-- The subject of the progressive's auxiliary. -/
def progressiveSubject : Slot String := { filler := .open_ .NOUN, gf := some .subj }

/-- The progressive's participial complement. -/
def progressiveComplement : Slot String := { filler := .open_ .VERB, gf := some .comp }

/-- The progressive construction (Figure 6): auxiliary *be* with a subject and a participial
complement. -/
def progressive : Construction (CompositionRule VendlerClass) :=
  { form :=
      [ progressiveSubject
      , { filler := .headed "be" .AUX, isHead := true }
      , progressiveComplement ]
  , meaning := progressiveRule }

/-- The valence set of the auxiliary *be*: its subject, of value `x`, and its participial
complement, of value `e`, whose subject requirement has value `s`. -/
def progressiveVal {E : Type*} (x e s : E) : List (Requirement E) :=
  [progressiveSubject.requirement x none, progressiveComplement.requirement e (some s)]

/-- Figure 6: the progressive is an instance of [kay-fillmore-1999]'s coinstantiation, which
unifies the subject requirement of the participial complement with the subject of *be*, the
raising property of the auxiliary. -/
theorem progressive_coinstantiation {E : Type*} {x e s : E} :
    Coinstantiates (progressiveVal x e s) ↔ s = x := by
  simpa [progressiveVal, Slot.requirement, progressiveSubject, progressiveComplement] using
    coinstantiates_subj_comp_iff (x := x) (e := e) (s := s)

/-! ### Concord vs. shift ((27), (28)) -/

/-- A unary rule preserves type when its output type is its input's —
(27)'s concord constructions; (28)'s shift constructions fail it. -/
def PreservesType (r : CompositionRule VendlerClass) : Prop :=
  ∀ p q, r [p] = some q → q = p

theorem frameAdverbial_concord : PreservesType frameAdverbialRule := by
  intro p q h
  simp only [frameAdverbialRule] at h
  split at h
  · exact (Option.some_inj.mp h).symm
  · exact absurd h (by simp)

theorem progressive_shift : ¬ PreservesType progressiveRule := fun h ↦
  absurd (h .activity .state (by decide)) (by decide)

/-! ### Frame-adverbial predictions (§5.1.2) -/

-- Figure 5
theorem frame_adverbial_instantiation :
    frameAdverbialRule.override reconciliation [.accomplishment]
      = [.accomplishment] :=
  CompositionRule.override_eq_of_eq_some _ (by decide)

-- (30)
theorem frame_adverbial_coerces_state :
    frameAdverbialRule.override reconciliation [.state]
      = [.achievement] := by decide

/-- An activity under a frame adverbial is ambiguous between accomplishment and achievement
readings, as in Ex. (41) ([de-swart-1998]). -/
theorem frame_adverbial_activity_ambiguity :
    frameAdverbialRule.override reconciliation [.activity]
      = [.accomplishment, .achievement] := by decide

/-! ### Progressive predictions (§5.2.1) -/

-- Figure 6
theorem progressive_explicit :
    progressiveRule [.activity] = some .state := by decide

-- (31), (42), (44)
theorem progressive_coerces_state :
    progressiveRule.override [conformToActivity] [.state]
      = [.state] := by decide

theorem progressive_coerces_telic :
    progressiveRule.override [conformToActivity] [.accomplishment]
      = [.state] := by decide

/-- Progressive predications denote states whatever the Aktionsart of the
complement (§5.2.1): the apparent paradox of a stativizing construction
accepting stative input dissolves under the override. -/
theorem progressive_stativizes (p : VendlerClass) :
    progressiveRule.override [conformToActivity] [p] = [.state] := by
  cases p <;> decide

end Michaelis2004
