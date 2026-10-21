module

public import Studies.BeaversEtAl2021
public import Linglib.Semantics.Composition.EventIdentification
public import Linglib.Semantics.Events.Closure
public import Linglib.Semantics.Mereology.Relation
public import Linglib.Data.Examples.YuAusensiSmith2023

/-!
# Yu, Ausensi & Smith (2023): States and Changes-of-State in the Semantics of Result Roots

This file formalizes the account of result roots by Yu, Ausensi and Smith. Beavers and
Koontz-Garboden's two classes of result roots, property concept roots and the roots that entail
change, here called change-of-state roots, differ in semantic type. A property concept root, such
as that of *open*, relates an individual to a state (20); a change-of-state root, such as that of
*break*, relates an individual to an event of change into the state it names (19)
(`Analysis.denote`). Events and states are sorts of one domain of eventualities, and the sorts
restrict the variables of the denotations, not the relations of becoming and causing.

A reading is available for a root when some model realizes it (`Available`), and the sort of the
root decides it (`available_iff`). Restitutive *again* needs a state that no change gave rise to,
the internal reading of a *for*-phrase a state of the root, and modification of a resultative
verb phrase by Event Identification an event of the root (`eventIdentification_states_eq_bot`);
the readings at the verb phrase are always available, *Lucy broke the vase* (21) among them, and a
denial that anything came to be in the root's state never is. No reading the account cannot
derive is accepted in the examples (`rows_unavailable`), and every derivable one they reject is a
resultative on a change-of-state root (`rows_available`), whose deviance the paper puts down to
direct causation and world knowledge.

On Beavers and Koontz-Garboden's analysis a change-of-state root is a stative description that
entails change (`BeaversEtAl2021.resultStative`). It predicts the same readings except the
internal reading of a *for*-phrase, which the examples reject (`rows_beaversKoontzGarboden`). Its
resultative conjoins the root with the result phrase by Event Identification (55), which makes
one state a state of both; once each state has one holder, the Unique Role Requirement (56), the
individual in the root's state is the holder of the result (`holder_eq_of_up`). On this analysis
the holder of the root's state is existentially closed in a state of its own, so in *a couple of
monks broke the corpse loose from the deck* it is the deck that breaks (`Monks.sentence`).

## Implementation notes

* The causative head vCAUSE is `EventStructure.Interpretation.vCause` restricted to events. It
  introduces no individual and quantifies over a caused eventuality of either sort (footnote 7).
* A model is an `Interpretation` with `State` and `Event` both the domain of eventualities and a
  predicate picking out the states (footnote 6).
* The existential closure of the holder at the verb phrase is `Event.closure` of the flipped
  relation, and the agent of (33) is the effector of the change (footnote 17).
* Beavers and Koontz-Garboden's first objection to (55), that one state cannot carry two
  unrelated descriptions, is an intuition the paper does not make precise; only the second, the
  Unique Role Requirement, is formalized.

## TODO

* Direct causation (pp. 1609–1610) is not represented, since `cause` is uninterpreted.
* The part-whole construals of (40)–(41) and the state-specifying result phrases of (47)–(48) are
  not represented.
* Footnote 11 records a reviewer who accepts internal readings in context, the only diagnostic
  that tells the two analyses apart.

## References

* [yu-ausensi-smith-2023]
* [beavers-koontz-garboden-2020]
* [kratzer-1996]
* [landman-2000]
-/

@[expose] public section

namespace YuAusensiSmith2023

open ArgumentStructure ArgumentStructure.EventStructure ModalLogic
open scoped SetRel

/-! ### Roots of two types -/

/-- The two classes of result roots (footnotes 1 and 4). -/
inductive RootClass
  /-- Roots that do not entail change, such as that of *open*. -/
  | propertyConcept
  /-- Roots that entail change, Beavers and Koontz-Garboden's result roots, such as that of
  *break*. -/
  | changeOfState
  deriving DecidableEq

/-- The two analyses of change-of-state roots. -/
inductive Analysis
  | yuAusensiSmith
  | beaversKoontzGarboden
  deriving DecidableEq

section Roots

variable {Entity Ev : Type*} (M : Interpretation Entity Ev Ev) (IsState : Ev → Prop)

/-- The events among the eventualities of `P`. -/
def events (P : Ev → Prop) (e : Ev) : Prop := P e ∧ ¬ IsState e

/-- The states among the eventualities of `P`. -/
def states (P : Ev → Prop) (s : Ev) : Prop := P s ∧ IsState s

/-- The root of a class with state description `B`. A property concept root relates an
individual to a state of `B` (20). A change-of-state root relates an individual to an event of
change into a state of `B` (19) on this paper's analysis, and to a state of `B` that a change gave
rise to (54a) on Beavers and Koontz-Garboden's. -/
def Analysis.denote : Analysis → RootClass → (Entity → Ev → Prop) → Entity → Ev → Prop
  | _, .propertyConcept, B, x => states IsState (B x)
  | .yuAusensiSmith, .changeOfState, B, x => events IsState (M.vBecome B x)
  | .beaversKoontzGarboden, .changeOfState, B, x =>
    states IsState (BeaversEtAl2021.resultStative M B x)

variable {IsState}

theorem disjoint_events_states (P Q : Ev → Prop) : Disjoint (events IsState P) (states IsState Q) :=
  Pi.disjoint_iff.2 fun _ ↦ Prop.disjoint_iff.2 fun ⟨⟨_, h⟩, _, h'⟩ ↦ h h'

/-- A root that holds of states, a property concept root among them, cannot modify a causative
verb phrase by Event Identification (30), (31). -/
theorem eventIdentification_states_eq_bot (B : Entity → Ev → Prop) (V : Ev → Prop) :
    eventIdentification (fun x ↦ states IsState (B x)) (events IsState V) = ⊥ :=
  eventIdentification_eq_bot_iff.2 fun _ ↦ (disjoint_events_states _ _).symm

end Roots

/-! ### Readings -/

/-- The readings the examples test. -/
inductive Reading
  /-- *Again* presupposes an earlier state that no change gave rise to. -/
  | restitutive
  /-- *Again* presupposes an earlier event of the verb phrase. -/
  | repetitive
  /-- A *for*-phrase measures an event of the verb phrase. -/
  | durative
  /-- A *for*-phrase measures a state of the root. -/
  | internal
  /-- The root modifies a causative verb phrase. -/
  | modifier
  /-- A resultative on the root continues with a denial that anything came to be in the root's
  state. -/
  | denial
  deriving DecidableEq

section Realized

variable {Entity Ev : Type*} (M : Interpretation Entity Ev Ev) (IsState : Ev → Prop)
  (R : SetRel Ev Ev) (L : Ev → Prop) (ρ : Entity → Ev → Prop) (x : Entity)

/-- The root `ρ`, applied to `x`, realizes the reading, with `R` relating an eventuality to the
earlier ones and `L` the result phrase of a resultative. The causative verb phrase over the root is
`events IsState (M.vCause (ρ x))`. -/
def Reading.Realized : Reading → Prop
  | .restitutive => ∃ v, ◇[R] (fun w ↦ ρ x w ∧ IsState w ∧ ∀ e, ¬ M.become w e) v
  | .repetitive => ∃ v, ◇[R] (events IsState (M.vCause (ρ x))) v
  | .durative => ∃ v, events IsState (M.vCause (ρ x)) v
  | .internal => ∃ v, states IsState (ρ x) v
  | .modifier => ∃ v, eventIdentification ρ (events IsState (M.vCause L)) x v
  | .denial => ∃ v, eventIdentification ρ (events IsState (M.vCause L)) x v ∧ ∀ y, ¬ ρ y v

end Realized

/-- The reading `r` is available for a root of class `c` on the analysis `a` when some model
realizes it. -/
def Available (a : Analysis) (c : RootClass) (r : Reading) : Prop :=
  ∃ (Ev : Type) (M : Interpretation Unit Ev Ev) (IsState : Ev → Prop) (B : Unit → Ev → Prop)
    (R : SetRel Ev Ev) (L : Ev → Prop), r.Realized M IsState R L (a.denote M IsState c B) ()

/-- The root describes states: always on Beavers and Koontz-Garboden's analysis, and on this one
when it is a property concept root. -/
def Analysis.DescribesStates : Analysis → RootClass → Prop
  | .yuAusensiSmith, c => c = .propertyConcept
  | .beaversKoontzGarboden, _ => True

instance : ∀ a c, Decidable (Analysis.DescribesStates a c)
  | .yuAusensiSmith, c => inferInstanceAs (Decidable (c = _))
  | .beaversKoontzGarboden, _ => inferInstanceAs (Decidable True)

/-- What the sort of the root predicts: the readings at the verb phrase always, the restitutive
reading for a root that entails no change, the internal reading for a root that describes states,
the modifier for one that describes events, and the denial never. -/
def Analysis.Predicts (a : Analysis) (c : RootClass) : Reading → Prop
  | .restitutive => c = .propertyConcept
  | .repetitive | .durative => True
  | .internal => a.DescribesStates c
  | .modifier => ¬ a.DescribesStates c
  | .denial => False

instance (a : Analysis) (c : RootClass) : DecidablePred (a.Predicts c) := fun r ↦ by
  cases r <;> unfold Analysis.Predicts <;> infer_instance

/-! ### A scene for every available reading -/

/-- The eventualities of a scene: a causing event, the change it causes, the state the change
gives rise to, and an earlier state that no change gave rise to. -/
inductive Scene
  | causing
  | change
  | result
  | prior
  deriving DecidableEq

/-- The causing event causes the change and its state, and the change causes its state. -/
def scene : Interpretation Unit Scene Scene where
  become s e := s = .result ∧ e = .change
  cause e v := e = .causing ∧ (v = .change ∨ v = .result) ∨ e = .change ∧ v = .result
  effector _ e := e = .causing

/-- The states of the scene. -/
def Scene.IsState (v : Scene) : Prop := v = .result ∨ v = .prior

/-! ### Predictions -/

variable {a : Analysis} {c : RootClass}

private theorem available_of {r : Reading}
    (h : r.Realized scene Scene.IsState ⊤ (· = .result)
      (a.denote scene Scene.IsState c fun _ ↦ Scene.IsState) ()) : Available a c r :=
  ⟨Scene, scene, Scene.IsState, fun _ ↦ Scene.IsState, ⊤, (· = .result), h⟩

/-- A state that no change gave rise to is available exactly for a property concept root, on
both analyses. -/
theorem available_restitutive_iff : Available a c .restitutive ↔ c = .propertyConcept := by
  refine ⟨fun ⟨_, M, _, B, R, _, _, _, _, hρ, hs, hb⟩ ↦ ?_, fun hc ↦ available_of ?_⟩
  · cases c
    · rfl
    · cases a
      · exact absurd hs hρ.2
      · obtain ⟨⟨_, e, he⟩, _⟩ := hρ
        exact absurd he (hb e)
  · subst hc
    exact ⟨.prior, .prior, trivial, by cases a <;> simp [Analysis.denote, states, Scene.IsState,
      scene]⟩

/-- The internal reading needs a root that describes states. -/
theorem available_internal_iff : Available a c .internal ↔ a.DescribesStates c := by
  refine ⟨fun ⟨_, M, IsState, B, R, _, v, hρ, hs⟩ ↦ ?_, fun h ↦ available_of ⟨.result, ?_⟩⟩
  · cases a <;> cases c
    · rfl
    · exact absurd hs hρ.2
    all_goals trivial
  · cases a <;> cases c <;>
      simp_all [Analysis.denote, Analysis.DescribesStates, states, Scene.IsState,
        BeaversEtAl2021.resultStative, scene]

/-- The modifier needs a root that describes events. -/
theorem available_modifier_iff : Available a c .modifier ↔ ¬ a.DescribesStates c := by
  refine ⟨fun ⟨_, M, IsState, B, R, L, v, hρ, hv⟩ hd ↦ ?_, fun hd ↦ available_of ?_⟩
  · cases a <;> cases c
    · exact hv.2 hρ.2
    · cases hd
    all_goals exact hv.2 hρ.2
  · cases a <;> cases c <;> simp only [Analysis.DescribesStates, not_true_eq_false] at hd
    exact ⟨.change, ⟨⟨.result, ⟨rfl, rfl⟩, .inl rfl⟩, by simp [Scene.IsState]⟩,
      ⟨.result, .inr ⟨rfl, rfl⟩, rfl⟩, by simp [Scene.IsState]⟩

/-- The causative verb phrase over any root is realized, *Lucy broke the vase* (21) and *Kim
opened the door* (22) among them, and so are the readings of *again* and of a *for*-phrase that
attach to it. -/
theorem available_durative : Available a c .durative := by
  refine available_of ⟨.causing, ?_, by simp [Scene.IsState]⟩
  cases c
  · exact ⟨.result, .inl ⟨rfl, .inr rfl⟩, by cases a <;> simp [Analysis.denote, states,
      Scene.IsState]⟩
  · cases a
    · exact ⟨.change, .inl ⟨rfl, .inl rfl⟩, ⟨.result, ⟨rfl, rfl⟩, .inl rfl⟩,
        by simp [Scene.IsState]⟩
    · exact ⟨.result, .inl ⟨rfl, .inr rfl⟩, ⟨⟨.inl rfl, .change, rfl, rfl⟩, .inl rfl⟩⟩

theorem available_repetitive : Available a c .repetitive :=
  let ⟨_, M, IsState, B, _, L, v, hv⟩ := available_durative (a := a) (c := c)
  ⟨_, M, IsState, B, ⊤, L, v, v, trivial, hv⟩

/-- No root survives a denial that anything came to be in its state. -/
theorem not_available_denial : ¬ Available a c .denial :=
  fun ⟨_, _, _, _, _, _, _, ⟨hρ, _⟩, hn⟩ ↦ hn _ hρ

/-- Availability is the prediction of the sort of the root. -/
theorem available_iff : ∀ r, Available a c r ↔ a.Predicts c r
  | .restitutive => available_restitutive_iff
  | .repetitive => iff_of_true available_repetitive trivial
  | .durative => iff_of_true available_durative trivial
  | .internal => available_internal_iff
  | .modifier => available_modifier_iff
  | .denial => iff_of_false not_available_denial id

/-! ### Beavers and Koontz-Garboden's resultative -/

section UniqueRole

variable {Entity Ev : Type*} {M : Interpretation Entity Ev Ev} {IsState : Ev → Prop}
  {B : Entity → Ev → Prop} {L : Ev → Prop} {holder : Entity → Ev → Prop} {c x : Entity} {s : Ev}

/-- Beavers and Koontz-Garboden's resultative conjoins the change-of-state root with the result
phrase by Event Identification (55), so one state is a state of both. Once each state has one
holder (56) and each description entails its holder, the individual in the root's state is the
holder of the result. -/
theorem holder_eq_of_up (hU : Mereology.UP holder) (hB : ∀ x s, B x s → holder x s)
    (hL : ∀ s, L s → holder c s)
    (h : eventIdentification (Analysis.beaversKoontzGarboden.denote M IsState .changeOfState B) L
      x s) : x = c :=
  hU (hB x s h.1.1.1) (hL s h.2)

end UniqueRole

/-! ### Breaking the corpse loose -/

namespace Monks

/-- The participants of *a couple of monks broke the corpse loose from the deck*. -/
inductive Entity
  | monks
  | corpse
  | deck
  deriving DecidableEq

/-- The eventualities of the sentence: the breaking, the broken state of the deck, and the
corpse's state of being loose from it. -/
inductive Ev
  | breaking
  | broken
  | loose
  deriving DecidableEq

/-- The breaking gives rise to the broken state and causes the loose one, and the monks are its
effector. -/
def model : Interpretation Entity Ev Ev where
  become s e := s = .broken ∧ e = .breaking
  cause e s := e = .breaking ∧ s = .loose
  effector x e := x = .monks ∧ e = .breaking

/-- The states of the scene. -/
def IsState (v : Ev) : Prop := v ≠ .breaking

/-- The deck holds the broken state and the corpse the loose one. -/
def holder (x : Entity) (v : Ev) : Prop := x = .deck ∧ v = .broken ∨ x = .corpse ∧ v = .loose

/-- *Broken*. -/
def broken (x : Entity) (s : Ev) : Prop := holder x s ∧ s = .broken

/-- *The corpse loose from the deck*. -/
def looseFromDeck (s : Ev) : Prop := holder .corpse s ∧ s = .loose

/-- Each state of the scene has one holder. -/
theorem up_holder : Mereology.UP holder := by
  rintro x y v (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) (⟨rfl, hv⟩ | ⟨rfl, hv⟩) <;> first | rfl | cases hv

/-- The sentence (34): the monks are the agent of an event of something becoming broken that
causes the corpse to be loose from the deck, and the thing that became broken is the deck. -/
theorem sentence :
    eventIdentification model.effector
        (Event.closure (flip (eventIdentification
          (Analysis.yuAusensiSmith.denote model IsState .changeOfState broken)
          (events IsState (model.vCause looseFromDeck))))) .monks .breaking ∧
      ∀ x, Analysis.yuAusensiSmith.denote model IsState .changeOfState broken x .breaking ↔
        x = .deck := by
  refine ⟨⟨⟨rfl, rfl⟩, .deck, ⟨⟨.broken, ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, rfl⟩, ?_⟩,
    ⟨.loose, ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩, rfl⟩, ?_⟩, fun x ↦ ?_⟩
  · simp [IsState]
  · simp [IsState]
  · cases x <;> simp [Analysis.denote, events, Interpretation.vBecome, model, broken, holder,
      IsState]

end Monks

/-! ### The examples -/

/-- The class of a row's root. -/
def rootClass? (d : Datum) : Option RootClass :=
  d.parse? "root class"
    [("property concept", .propertyConcept), ("change of state", .changeOfState)]

/-- The readings a row tests, with their judgments: a resultative tests the modifier and a denial
the denial, each judged as the sentence, and the other rows the readings they name. -/
def tests (d : Datum) : List (Reading × Judgment) :=
  match d.feature? "diagnostic" with
  | some "resultative modifier" => [(.modifier, d.judgment)]
  | some "entailment denial" => [(.denial, d.judgment)]
  | _ => d.readings.filterMap fun r ↦
    ([("restitutive", Reading.restitutive), ("repetitive", .repetitive),
      ("durative", .durative), ("internal", .internal)].lookup r.1).map (·, r.2)

/-- No reading the account cannot derive is accepted in the examples. -/
theorem rows_unavailable : ∀ d ∈ Examples.all, ∀ c ∈ rootClass? d, ∀ t ∈ tests d,
    ¬ Available .yuAusensiSmith c t.1 → t.2 ≠ .acceptable := by
  simp only [available_iff]
  decide

/-- Every derivable reading the examples reject is a resultative on a change-of-state root, judged
so by a source the paper cites or, for (44), questionable. -/
theorem rows_available : ∀ d ∈ Examples.all, ∀ c ∈ rootClass? d, ∀ t ∈ tests d,
    Available .yuAusensiSmith c t.1 → t.2 ≠ .acceptable →
      t.1 = .modifier ∧ c = .changeOfState ∧
        (d.feature? "judgedBy" ≠ none ∨ t.2 = .questionable) := by
  simp only [available_iff]
  decide

/-- On Beavers and Koontz-Garboden's analysis a reading other than the modifier is accepted
exactly when it is available, except the internal reading with a change-of-state root (§4.1). -/
theorem rows_beaversKoontzGarboden : ∀ d ∈ Examples.all, ∀ c ∈ rootClass? d, ∀ t ∈ tests d,
    t.1 ≠ .modifier → ((t.2 = .acceptable ↔ Available .beaversKoontzGarboden c t.1) ↔
      ¬ (c = .changeOfState ∧ t.1 = .internal)) := by
  simp only [available_iff]
  decide

end YuAusensiSmith2023
